-- Prove2me | Theorems.Thm_FamilyGenTest_eq_4
-- name    : FamilyGenTest.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:46.868981+00:00
-- url     : https://prove2.me/theorems/40eac80a-2436-4746-bba6-00af6ec68985
-- title:
--   Eq. (4) — $V^*$ of (3) solves the optimality equations; optimal rules exist and are the greedy ones
-- statement:
--   At every feasible state $\mathbf s$,
--   $$
--   V^*(\mathbf s)=\max\Bigl\{\max_{i\in\mathcal I\setminus\mathbf s}\mathbb E_i[r_i(\mathbb P_i(\mathbf S'))-c_i(\mathbf s)+V^*(\mathbf S')\mid\mathbf s],\ \sum_{i\in\mathcal I\setminus\mathbf s}\bar r_i(\mathbb P_i(\mathbf s))\Bigr\},
--   $$
--   where $V^*$ is the maximum of (3) over decision rules. Moreover an optimal rule exists, and a rule is optimal if and only if at every feasible state its action solves the right-hand side.
--
--   This connects the objective (3), a maximum over rules, with the one-step equation that the threshold argument analyzes.
--
--   **Formalization Note** The maximum in the first display is written over $\mathcal A_{\mathbf s}$, so that it stays defined when nobody is untested.
--
--   Differences from the source:
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - generalization: the Mendelian prior (5) → an arbitrary mass function on $\{0,1,2\}^{\mathcal I}$; reason: the argument does not use the pedigree and p.11 says priors incorporate all prior information; (5) is the special case given by the theorem eq_5_mendelian_prior
--   - encoding: a state as a partition $\{s_0,s_1,s_2\}$ of the tested individuals, state space $\mathcal S=\{\mathbf s:\exists g\in\mathcal G(\mathbf s)\}$ → `State I := I → Option (Fin 3)`, with `Feasible` meaning $\mathbb P(G\in\mathcal G(\mathbf s))>0$; reason: same objects when $\mathcal G$ is the support of the prior; the family is a `Fintype`, possibly empty
--   - encoding: $r_i(\mathbb P_i(\mathbf S'))$ with Definition 3 and Assumption 1 → `testedReward`: $r_i^0(0)$ at result $0$, $r_i^1(1)$ at results $1,2$; reason: after a test the belief is the true carrier status, which is what Assumption 1 and Definition 3 give
--   - encoding: $V^*$ as the maximum of (3), an expectation over sample paths with absorbing state $\Delta$ and action $C$, undefined at infeasible states → `Vstar`: the maximum over the finite type `Policy I` of the posterior average of a rolled-out return, with no $\Delta$ and no $C$; $V^*=0$ at infeasible states; reason: given $G=g$ and the rule the path is determined, so the two expectations agree; the infeasible children enter only with coefficient $0$
--   - encoding: $\max\{\max_{i\in\mathcal I\setminus\mathbf s}\dots,\sum\dots\}$ → a maximum over $\mathcal A_{\mathbf s}=(\mathcal I\setminus\mathbf s)\cup\{\varnothing\}$; reason: same maximum, and it stays defined when nobody is untested
--   - generalization: the reward assumptions of §4 → arbitrary real rewards and costs; reason: the statement does not depend on them, and every instance of the source is covered
--   - generalization: the optimal policy is obtained by solving the right-hand side of (4), and there exists an optimal policy → a rule is optimal iff at every feasible state it solves the right-hand side of (4), and an optimal rule exists; reason: the source's direction is one half of the equivalence
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), (3), p.10; (4), p.11; "there exists an optimal policy that is Markovian, stationary, and deterministic", p.10

import Mathlib
import Definitions.Def_FamilyGenTest_Vstar

namespace FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Eq. (4) with the existence claim of p.10 (Adelman & Wang, Optimal Genetic Testing of Families,
SSRN 4624694 (Jan 24 2023), pp.10–11): at every feasible state, `V*`, the maximum of (3), solves the
optimality equations (4), written as a maximum over `𝒜_s = (I \ s) ∪ {∅}`; an optimal rule exists;
and a rule is optimal iff at every feasible state its action solves the right-hand side of (4). -/
theorem eq_4 (R : Rewards I) (μ : Prior I) :
    (∀ s, Feasible μ s →
      Vstar R μ s = (actionSet s).sup' (Finset.insert_nonempty _ _) (actionValue R μ s)) ∧
    (∃ π : Policy I, IsOptimal R μ π) ∧
    ∀ π : Policy I, IsOptimal R μ π ↔ IsGreedy R μ π := by sorry

end FamilyGenTest
