#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <limits.h>

struct solu_node
{
    int level;
    int size;
    int *solu;
    struct solu_node *next;
    struct solu_node *pre;
};

struct CNF_node
{
    int e;
    int *clause_num;
    int **clause;
};

struct cdcl_node
{
    int level;
    int *cur_l_solu;
    int cur_l_solu_num;
};

struct CNF_node *CNF_list;
struct solu_node *solu_list = NULL;
struct solu_node *solu_path;
struct cdcl_node *cdcl;

void build_instance(char *);
void dominating(int);
void kc(int);
int unit_propagation(int *, int, int);
int unit_propagation_cl (int *, int, int);
void conflict_analysis(int);
void free_all();
int conflict_clause;
int conflict_variable;

void out_file();
int v, pe, temp_pe;
int **prop_clause;
int **orig_clause_no;
int *prop_clause_num;
int *selected_clause;
int **partial_solution;
int *solution;
int solution_size;
int *psc_num;
int partial_length;
int max_clause_length = 0;
int dom_sum = 0;

int *is_select_c;
int *is_select_v;


int *e_in_cc;
int *v_in_c_num;
int *l_in_c_num;

int partial_solution_num;
int selected_clause_num;
char *input_file;
int abs(int);

int main(int argc, char *argv[])
{
    int i, j, t, sum = 0;
    double model_sum = 0;
    int solu_sum = 0;
    int solu_length;
    input_file = argv[1];
    puts(input_file);
    build_instance(input_file);
    dominating(0);
    kc(0);
    struct solu_node *temp;
    i = 0;
    while(1)
    {
        temp = solu_list;
        if(temp == NULL) break;
        solu_path[temp->level] = *temp;
        solu_list = solu_list->next;
        t = unit_propagation(temp->solu, temp->size, temp->level);
        if(t == 1)
        {
            solu_sum++;
            solu_length = 0;
            memset(solution, 0, (v+1)*sizeof(int));
            for(i = 0; i <= temp->level; i++)
            {
                solu_length += solu_path[i].size;
                if(cdcl[i].cur_l_solu_num != solu_path[i].size)
                {
                    printf("error!\n");
                    exit(0);
                }
                for(j = 0; j < cdcl[i].cur_l_solu_num; j++)
                {
                    solution[abs(cdcl[i].cur_l_solu[j])] = cdcl[i].cur_l_solu[j];
                }
            }
            model_sum += pow(2, v-solu_length);
            ++sum;
            free(temp->solu);
            temp->solu = NULL;
            free(temp);
            temp = NULL;
            printf("SAT\n");
            free_all();
            return 10;
        }
        else if(t == 2)
        {
            free(temp->solu);
            temp->solu = NULL;
            free(temp);
            temp = NULL;
            continue;
        }
        else if(t == 3)
        {
            free(temp->solu);
            temp->solu = NULL;
            free(temp);
            temp = NULL;
            continue;
        }
        dominating(temp->level+1);
        kc(temp->level+1);
        free(temp->solu);
        temp->solu = NULL;
        free(temp);
        temp = NULL;
    }

    printf("UNSAT\n");
    free_all();
    return 20;
}

void build_instance(char * filename)
{
    int i, j, k, t, p;
    int e;
    FILE *fp;
    int temp_l[100];
    char temp[100];
    char temp1[100];
    fp = fopen(filename, "r");
    fgets(temp, 100, fp);
    while(temp[0]!='p')
    {
        fgets(temp, 100, fp);
    }
    sscanf(temp, "%s%s%d%d", temp1, temp1, &v, &e);
    CNF_list = (struct CNF_node*)malloc(v*sizeof(struct CNF_node));
    orig_clause_no = (int **)malloc(v*sizeof(int*));
    CNF_list[0].clause = (int **)malloc(e*sizeof(int *));
    CNF_list[0].clause_num = (int *)malloc(e*sizeof(int));
    CNF_list[0].e = e;
    psc_num = (int *)malloc((v+10)*sizeof(int));
    solution = (int *)malloc((v+1)*sizeof(int));
    partial_solution = (int **)malloc((v+10)*sizeof(int *));
    selected_clause = (int *)malloc(e*sizeof(int));
    prop_clause = (int **)malloc(e*sizeof(int *));
    prop_clause_num = (int *)malloc(e*sizeof(int));
    solu_path = (struct solu_node *)malloc(v*sizeof(struct solu_node));
    cdcl = (struct cdcl_node *)malloc(v*sizeof(struct cdcl_node));

    is_select_c = (int *)malloc(e*sizeof(int));
    is_select_v = (int *)malloc((v+1)*sizeof(int));
    e_in_cc = (int *)malloc((e+1)*sizeof(int));
    v_in_c_num = (int *)malloc((v+1)*sizeof(int));
    l_in_c_num = (int *)malloc((2*v+1)*sizeof(int));

    memset(e_in_cc, 0, (e+1)*sizeof(int));
    memset(v_in_c_num, 0, (v+1)*sizeof(int));
    memset(l_in_c_num, 0, (2*v+1)*sizeof(int));

    dom_sum = log(v)/log(2)-2;
    partial_length = 10+log(v)/log(2);
    for(i = 0; i < v; ++i)
    {
        partial_solution[i] = (int *)malloc(partial_length*sizeof(int));
        orig_clause_no[i] = (int *)malloc(e*sizeof(int));
        memset(partial_solution[i], 0, partial_length*sizeof(int));
        cdcl[i].cur_l_solu = (int *)malloc((v+1)*sizeof(int));
    }
    for(i = 0; i < e; ++i)
    {
        orig_clause_no[0][i] = i;
        k = 0;
        fscanf(fp, "%d", &t);
        while(t != 0)
        {
            temp_l[k++] = t;
            p = abs(t);
            ++v_in_c_num[p];
            ++l_in_c_num[v+t];
            fscanf(fp, "%d", &t);
        }
        CNF_list[0].clause_num[i] = k;
        CNF_list[0].clause[i] = (int *)malloc(k*sizeof(int));
        for(j = 0; j < k; ++j)
        {
            CNF_list[0].clause[i][j] = temp_l[j];
        }
        if(k > max_clause_length)
        {
            max_clause_length = k;
        }
    }
    for(i = 0; i < e; ++i)
    {
        prop_clause[i] = (int *)malloc((max_clause_length+1)*sizeof(int));
    }
}

void free_all()
{
    int i, j;

    for(i = 0; i < CNF_list[0].e; ++i)
    {
        free(prop_clause[i]);
    }
    free(prop_clause);
    for(i = 0; ; ++i)
    {
        if(CNF_list[i].clause == NULL)
        {
            break;
        }
        else
        {
            for(j = 0; j < CNF_list[i].e; ++j)
            {
                free(CNF_list[i].clause[j]);
            }
            free(CNF_list[i].clause);
            free(CNF_list[i].clause_num);
        }
    }
    free(CNF_list);
    for(i = 0; i < v; ++i)
    {
        free(partial_solution[i]);
        free(orig_clause_no[i]);
        free(cdcl[i].cur_l_solu);
    }
    free(partial_solution);
    free(orig_clause_no);
    free(cdcl);
    free(psc_num);
    free(solution);
    free(selected_clause);
    free(solu_path);
    free(is_select_c);
    free(is_select_v);
    free(e_in_cc);
}

void dominating(int m)
{
    int i, j, k, t, max = 0, max_id = -1, temp;
    int sum = dom_sum;
    selected_clause_num = 0;
    memset(is_select_c, 0, CNF_list[m].e*sizeof(int));
    memset(is_select_v, 0, (v+1)*sizeof(int));
    k = 0;
    while(k < sum)
    {
        max = INT_MIN;
        max_id = -1;
        for(i = 0; i < CNF_list[m].e; ++i)
        {
            temp = 0;
            if(is_select_c[i] == 1 || CNF_list[m].clause_num[i] > 2) continue;

            for(j = 0; j < CNF_list[m].clause_num[i]; ++j)
            {
                t = abs(CNF_list[m].clause[i][j]);
                temp += v_in_c_num[t];
            }

            temp += e_in_cc[orig_clause_no[m][i]]*2;
            if(temp > max)
            {
                max = temp;
                max_id = i;
            }
        }

        if(max == INT_MIN)
        {
            for(i = 0; i < CNF_list[m].e; ++i)
            {
                temp = 0;
                if(is_select_c[i] == 1) continue;

                for(j = 0; j < CNF_list[m].clause_num[i]; ++j)
                {
                    t = abs(CNF_list[m].clause[i][j]);
                    temp += v_in_c_num[t];
                }

                temp += e_in_cc[orig_clause_no[m][i]];
                temp = temp/CNF_list[m].clause_num[i]/CNF_list[m].clause_num[i];
                if(temp > max)
                {
                    max = temp;
                    max_id = i;
                }
            }
            if(temp == 0)
            {
                break;
            }
        }

        is_select_c[max_id] = 1;
        selected_clause[selected_clause_num++] = max_id;
        for(i = 0; i < CNF_list[m].clause_num[max_id]; ++i)
        {
            t = abs(CNF_list[m].clause[max_id][i]);
            if(is_select_v[t] == 0)
            {
                is_select_v[t] = 1;
                ++k;
            }
        }
    }
}
void kc(int m)
{
    int i, j, t, v0, v1, vt, k, p, q, sign;
    int temp_clause[100], temp_clause_num = 0;
    partial_solution_num = 0;
    memset(psc_num, 0, v*sizeof(int));

    t = selected_clause[0];
    v0 = abs(CNF_list[m].clause[t][0]);
    v1 = abs(CNF_list[m].clause[t][1]);
    if(v_in_c_num[v0]+l_in_c_num[v+CNF_list[m].clause[t][0]] <  v_in_c_num[v1]+l_in_c_num[v+CNF_list[m].clause[t][1]])
    {
        vt = CNF_list[m].clause[t][0];
        CNF_list[m].clause[t][0] = CNF_list[m].clause[t][1];
        CNF_list[m].clause[t][1] = vt;
    }

    for(i = 0; i < CNF_list[m].clause_num[t]; ++i)
    {
        for(k = 0; k < i; ++k)
        {
            partial_solution[partial_solution_num][psc_num[partial_solution_num]++] = -CNF_list[m].clause[t][k];
        }
        partial_solution[partial_solution_num][psc_num[partial_solution_num]++] = CNF_list[m].clause[t][k];
        ++partial_solution_num;
    }

    for(i = 1; i < selected_clause_num; ++i)
    {
        t = selected_clause[i];
        v0 = abs(CNF_list[m].clause[t][0]);
        v1 = abs(CNF_list[m].clause[t][1]);
        if(v_in_c_num[v0]+l_in_c_num[v+CNF_list[m].clause[t][0]] <  v_in_c_num[v1]+l_in_c_num[v+CNF_list[m].clause[t][1]])
        {
            vt = CNF_list[m].clause[t][0];
            CNF_list[m].clause[t][0] = CNF_list[m].clause[t][1];
            CNF_list[m].clause[t][1] = vt;
        }


        for(j = 0; j < partial_solution_num; ++j)
        {
            temp_clause_num = 0;
            for(k = 0; k < CNF_list[m].clause_num[t]; ++k)
            {
                sign = 0;
                for(q = 0; q < psc_num[j]; ++q)
                {
                    if(partial_solution[j][q] == CNF_list[m].clause[t][k])
                    {
                        sign = 1;
                        break;
                    }
                    else if(partial_solution[j][q] == -CNF_list[m].clause[t][k])
                    {
                        sign = -1;
                        break;
                    }
                }
                if(sign == 1)
                {
                    break;
                }
                else if(sign == 0)
                {
                    temp_clause[temp_clause_num++] = -CNF_list[m].clause[t][k];
                }
            }
            if(k == CNF_list[m].clause_num[t])
            {
                if(temp_clause_num == 0)
                {
                    memcpy(partial_solution[j], partial_solution[partial_solution_num-1], partial_length*sizeof(int));
                    psc_num[j] = psc_num[partial_solution_num-1];
                    --partial_solution_num;
                    --j;
                }
                else
                {
                    partial_solution[j][psc_num[j]++] = -temp_clause[0];
                    for(p = 1; p < temp_clause_num; ++p)
                    {
                        memcpy(partial_solution[partial_solution_num], partial_solution[j],partial_length*sizeof(int));
                        psc_num[partial_solution_num] = psc_num[j]-1;
                        for(q = 0; q < p; ++q)
                        {
                            partial_solution[partial_solution_num][psc_num[partial_solution_num]++] = temp_clause[q];
                        }
                        partial_solution[partial_solution_num][psc_num[partial_solution_num]++] = -temp_clause[q];
                        ++partial_solution_num;
                    }
                }
            }
        }
    }

    for(i = 0; i < partial_solution_num-1; i++)
    {
        if(psc_num[i] == psc_num[i+1])
        {
            t = 0;
            p = 0;
            for(j = 0; j < psc_num[i]; j++)
            {
                if(partial_solution[i][j] + partial_solution[i+1][j] == 0)
                {
                    vt = j;
                    t++;
                }
                else if(partial_solution[i][j] != partial_solution[i+1][j])
                {
                    break;
                }
            }
            if(j == psc_num[i] && t == 1)
            {
                partial_solution[i+1][vt] = partial_solution[i+1][psc_num[i+1]-1];
                psc_num[i+1]--;
                psc_num[i] = -1;
            }
        }
    }

    for(p = partial_solution_num-1; p >= 0; --p)
    {
        if(psc_num[p] == -1) continue;
        struct solu_node *temp;
        temp = (struct solu_node *)malloc(1*sizeof(struct solu_node));
        temp->solu = (int *)malloc(partial_length *sizeof(int));
        temp->size = psc_num[p];
        temp->level = m;
        temp->next = NULL;
        memcpy(temp->solu, partial_solution[p], partial_length *sizeof(int));
        if(solu_list == NULL)
        {
            solu_list = temp;
        }
        else
        {
            temp->next = solu_list;
            solu_list = temp;
        }
    }
}

int unit_propagation(int *part_solu, int n, int m)
{
    int i, j, t, p, sign;
    memset(solution, 0, (v+1)*sizeof(int));
    int pe = CNF_list[m].e;

    memcpy(prop_clause_num, CNF_list[m].clause_num, pe*sizeof(int));
    for(i = 0; i < pe; ++i)
    {
        memcpy(prop_clause[i], CNF_list[m].clause[i], prop_clause_num[i]*sizeof(int));
    }

    cdcl[m].cur_l_solu_num = 0;
    solution_size = n;
    for(i = 0; i < n; ++i)
    {
        t = part_solu[i];
        cdcl[m].cur_l_solu[cdcl[m].cur_l_solu_num] = t;
        solution[abs(t)] = t;
        ++cdcl[m].cur_l_solu_num;
    }

    temp_pe = pe;
    sign = 1;
    while(sign == 1)
    {
        sign = 0;
        for(i = 0; i < pe; ++i)
        {
            if(prop_clause_num[i] == -1) continue;
            for(j = 0; j < prop_clause_num[i]; ++j)
            {
                t = prop_clause[i][j];
                if(solution[abs(t)] == t)
                {
                    --temp_pe;
                    prop_clause_num[i] = -1;
                    break;
                }
                else if(solution[abs(t)]+t == 0)
                {
                    prop_clause[i][j] = prop_clause[i][prop_clause_num[i]-1];
                    --prop_clause_num[i];
                    --j;
                }
            }
            if(prop_clause_num[i] == 0)
            {
                t = prop_clause[i][0];
                conflict_clause = orig_clause_no[m][i];
                conflict_variable = abs(t);
                ++e_in_cc[conflict_clause];
                break;
            }
            if(prop_clause_num[i] == 1)
            {
                t = prop_clause[i][0];
                cdcl[m].cur_l_solu[cdcl[m].cur_l_solu_num] = t;
                ++cdcl[m].cur_l_solu_num;
                ++solution_size;
                solution[abs(t)] = t;
                prop_clause_num[i] = -1;
                --temp_pe;
                sign = 1;
            }
        }
        if(i < pe)
        {
            return 2;
        }
    }
    if(temp_pe == 0)
    {
        solu_path[m].size = solution_size;
        return 1;
    }
    solu_path[m].size = solution_size;
    CNF_list[m+1].e = temp_pe;
    if(CNF_list[m+1].clause == NULL)
    {
        p = CNF_list[0].e;
        CNF_list[m+1].clause = (int **)malloc(p*sizeof(int *));
        CNF_list[m+1].clause_num = (int *)malloc(p*sizeof(int));
        for(i = 0; i < p; ++i)
        {
            CNF_list[m+1].clause[i] =  (int *)malloc(max_clause_length*sizeof(int));
        }
    }

    t = 0;
    for(i = 0; i < pe; ++i)
    {
        if(prop_clause_num[i] == -1) continue;
        orig_clause_no[m+1][t] = orig_clause_no[m][i];
        CNF_list[m+1].clause_num[t] = prop_clause_num[i];
        memcpy(CNF_list[m+1].clause[t], prop_clause[i], prop_clause_num[i]*sizeof(int));
        ++t;
    }
    return 0;
}

