#include "ntr.h"
#include "cuddInt.h"
#include <ctype.h>
#include <string.h>

void customDumpDot(DdManager *dd, DdNode *f, const char *filename, char **varnames) {
    FILE *fp = fopen(filename, "w");
    if (!fp) {
        fprintf(stderr, "Failed to open file %s for writing.\n", filename);
        return;
    }
    
    int used_vars[100] = {0};
    int max_used_var = -1;
    
    int traverseMaxNodeCount = 1000;
    DdNode **scanQueue = malloc(traverseMaxNodeCount * sizeof(DdNode*));
    int scanFront = 0, scanRear = 0;
    unsigned long *scanVisited = calloc(1000001, sizeof(unsigned long));
    
    scanQueue[scanRear++] = f;
    
    while (scanFront < scanRear) {
        DdNode *node = scanQueue[scanFront++];
        DdNode *regular = Cudd_Regular(node);
        unsigned long nodeAddr = (unsigned long)regular;
        
        if (scanVisited[nodeAddr % 1000000]) continue;
        scanVisited[nodeAddr % 1000000] = 1;
        
        if (!Cudd_IsConstant(regular)) {
            int index = Cudd_NodeReadIndex(regular);
            used_vars[index] = 1;
            if (index > max_used_var) max_used_var = index;
            
            DdNode *T = Cudd_T(regular);
            DdNode *E = Cudd_E(regular);
            if (!Cudd_IsConstant(T)) scanQueue[scanRear++] = T;
            if (!Cudd_IsConstant(Cudd_Regular(E))) scanQueue[scanRear++] = Cudd_Regular(E);
        }
    }
    free(scanQueue);
    free(scanVisited);
    
    fprintf(fp, "digraph \"DD\" {\n");
    fprintf(fp, "size = \"7.5,10\"\n");
    fprintf(fp, "center = true;\n");
    fprintf(fp, "edge [dir = none];\n");
    
    fprintf(fp, "{ node [shape = plaintext];\n");
    fprintf(fp, "  edge [style = invis];\n");
    fprintf(fp, "  \"CONST NODES\" [style = invis];\n");
    fprintf(fp, "  ");
    
    for (int i = 0; i <= max_used_var; i++) {
        if (used_vars[i]) {
            char varname[3] = {'a' + i, 0};
            fprintf(fp, "\" %s \" -> ", varnames && varnames[i] ? varnames[i] : varname);
        }
    }
    fprintf(fp, "\"CONST NODES\"; \n}\n");
    
    fprintf(fp, "{ rank = same; node [shape = box]; edge [style = invis];\n");
    fprintf(fp, "\"F\"; }\n");
    
    int maxNodeCount = 1000;
    DdNode **queue = malloc(maxNodeCount * sizeof(DdNode*));
    int front = 0, rear = 0;
    
    unsigned long maxAddr = 1000000;
    char *visited = calloc(maxAddr + 1, 1);
    
    DdNode *one = Cudd_ReadOne(dd);
    DdNode *zero = Cudd_Not(one);
    
    queue[rear++] = f;
    
    while (front < rear) {
        DdNode *node = queue[front++];
        DdNode *regular = Cudd_Regular(node);
        unsigned long nodeAddr = (unsigned long)regular;
        
        if (visited[nodeAddr % maxAddr]) continue;
        visited[nodeAddr % maxAddr] = 1;
        
        if (!Cudd_IsConstant(regular)) {
            int index = Cudd_NodeReadIndex(regular);
            char varname[3] = {'a' + index, 0};
            
            fprintf(fp, "{ rank = same; \" %s \";\n", varname);
            fprintf(fp, "\"0x%lx\" [label = \"%s\"];\n", nodeAddr, varname);
            fprintf(fp, "}\n");
            
            DdNode *T = Cudd_T(regular);
            DdNode *E = Cudd_E(regular);
            
            if (Cudd_IsComplement(node)) {
                T = Cudd_Not(T);
                E = Cudd_Not(E);
            }
            
            if (T == one) {
                fprintf(fp, "\"0x%lx\" -> \"0x%lx\";\n", nodeAddr, (unsigned long)one);
            } else if (T == zero) {
                fprintf(fp, "\"0x%lx\" -> \"0x0\";\n", nodeAddr);
            } else {
                fprintf(fp, "\"0x%lx\" -> \"0x%lx\";\n", nodeAddr, (unsigned long)Cudd_Regular(T));
                if (Cudd_IsComplement(T)) {
                    fprintf(fp, "\"0x%lx\" -> \"0x%lx\" [style=dotted];\n",
                            nodeAddr, (unsigned long)Cudd_Regular(T));
                }
                queue[rear++] = T;
            }
            
            if (E == one) {
                fprintf(fp, "\"0x%lx\" -> \"0x%lx\" [style=dashed];\n", 
                        nodeAddr, (unsigned long)one);
            } else if (E == zero) {
                fprintf(fp, "\"0x%lx\" -> \"0x0\" [style=dashed];\n", nodeAddr);
            } else {
                fprintf(fp, "\"0x%lx\" -> \"0x%lx\" [style=dashed];\n", 
                        nodeAddr, (unsigned long)Cudd_Regular(E));
                if (Cudd_IsComplement(E)) {
                    fprintf(fp, "\"0x%lx\" -> \"0x%lx\" [style=dotted];\n", 
                            nodeAddr, (unsigned long)Cudd_Regular(E));
                }
                queue[rear++] = E;
            }
        }
    }
    
    fprintf(fp, "{ rank = same; \"CONST NODES\";\n");
    fprintf(fp, "{ node [shape = box]; \"0x%lx\" [label = \"1\"];\n", (unsigned long)one);
    fprintf(fp, "\"0x0\" [label = \"0\"];\n");
    fprintf(fp, "}\n}\n");
    
    if (f == one) {
        fprintf(fp, "\"F0\" -> \"0x%lx\" [style = solid];\n", (unsigned long)one);
    } else if (f == zero) {
        fprintf(fp, "\"F0\" -> \"0x0\" [style = solid];\n"); 
    } else {
        fprintf(fp, "\"F0\" -> \"0x%lx\" [style = solid];\n", (unsigned long)Cudd_Regular(f));
    }
    
    fprintf(fp, "}\n");
    
    fclose(fp);
    free(visited);
    free(queue);
}

void removeSpaces(char* str) {
    int i = 0, j = 0;
    while (str[i]) {
        if (str[i] != ' ' && str[i] != '\t') {
            str[j++] = str[i];
        }
        i++;
    }
    str[j] = '\0';
}

DdNode* parseBooleanExpression(DdManager* dd, char* expr, char* varNames[], int* varCount) {
    DdNode* varNodes[26] = {NULL};
    char* expression = strdup(expr);
    removeSpaces(expression);
    
    DdNode* result = Cudd_ReadLogicZero(dd);
    Cudd_Ref(result);
    
    char* term = strtok(expression, "+");
    while (term != NULL) {
        DdNode* termNode = Cudd_ReadOne(dd);
        Cudd_Ref(termNode);
        
        for (int i = 0; i < strlen(term); i++) {
            if (isalpha(term[i])) {
                int varIndex = term[i] - 'a';
                int complement = 0;
                
                if (i + 1 < strlen(term) && term[i + 1] == '\'') {
                    complement = 1;
                    i++;
                }
                
                if (varNodes[varIndex] == NULL) {
                    varNodes[varIndex] = Cudd_bddNewVar(dd);
                    varNames[*varCount] = malloc(2);
                    varNames[*varCount][0] = 'a' + varIndex;
                    varNames[*varCount][1] = '\0';
                    (*varCount)++;
                }
                
                DdNode* var = varNodes[varIndex];
                if (complement) var = Cudd_Not(var);
                
                DdNode* temp = Cudd_bddAnd(dd, termNode, var);
                Cudd_Ref(temp);
                Cudd_RecursiveDeref(dd, termNode);
                termNode = temp;
            }
        }
        
        DdNode* temp = Cudd_bddOr(dd, result, termNode);
        Cudd_Ref(temp);
        Cudd_RecursiveDeref(dd, result);
        Cudd_RecursiveDeref(dd, termNode);
        result = temp;
        
        term = strtok(NULL, "+");
    }
    
    free(expression);
    return result;
}

int main(int argc, char **argv) {
    DdManager *dd = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    if (dd == NULL) {
        fprintf(stderr, "CUDD initialization failed.\n");
        exit(1);
    }

    Cudd_AutodynDisable(dd);
    
    printf("Enter a Boolean expression using variables a-z\n");
    printf("Legal operations: AND (concatenation or *), OR (+), NOT (')\n");
    
    char input[256];
    if (fgets(input, sizeof(input), stdin) == NULL) {
        Cudd_Quit(dd);
        return 1;
    }
    
    input[strcspn(input, "\n")] = '\0';
    
    char *varNames[26] = {NULL};
    int varCount = 0;
    
    DdNode* f = parseBooleanExpression(dd, input, varNames, &varCount);
    
    printf("\nROBDD for f = %s:\n", input);
    Cudd_PrintDebug(dd, f, varCount, varCount);
    
    if (f == Cudd_ReadOne(dd)) {
        printf("Function is a tautology.\n");
    } else {
        printf("Function evaluates to 0 for at least one input.\n");
    }
    
    const char *output_dir = "output";
    
    char dot_filepath[256], png_filepath[256];
    sprintf(dot_filepath, "%s/bdd.dot", output_dir);
    sprintf(png_filepath, "%s/bdd.png", output_dir);
    
    char *dot_var_names[100] = {NULL};
    for (int i = 0; i < varCount; i++) {
        int idx = Cudd_NodeReadIndex(Cudd_bddIthVar(dd, i));
        dot_var_names[idx] = varNames[i];
    }
    
    customDumpDot(dd, f, dot_filepath, dot_var_names);
    printf("DOT file saved @ %s\n", dot_filepath);
    
    char command[256];
    sprintf(command, "mkdir -p %s && dot -Tpng %s -o %s", output_dir, dot_filepath, png_filepath);
    if (system(command) == 0) {
        printf("PNG generated @ %s\n", png_filepath);
    } else {
        printf("Failed to generate PNG. Is GraphViz installed?\n");
    }
    
    Cudd_RecursiveDeref(dd, f);
    for (int i = 0; i < 26; i++) {
        if (varNames[i]) free(varNames[i]);
    }
    
    Cudd_Quit(dd);
    return 0;
}