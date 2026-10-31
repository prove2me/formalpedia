-- Prove2me | Theorems.Thm_FamilyGenTest_ec_2
-- name    : FamilyGenTest.ec_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:42.619063+00:00
-- url     : https://prove2.me/theorems/9acb4bb1-e3c8-41c2-8502-226cb761604b
-- title:
--   (EC.2) — the expected future value is linear in the risk
-- statement:
--   Let $\mathbf s$ be feasible and $i$ untested in $\mathbf s$. Then
--   $$
--   \mathbb E_i[V^*(\mathbf S')\mid\mathbf s]=\sum_{\gamma}\mathbb P(G_i=\gamma\mid\mathbf s)\,V^*(\mathbf s_\gamma\cup\{i\})=\Phi_i(\mathbf s)\mathbb P_i(\mathbf s)+V^*(\mathbf s_0\cup\{i\}).
--   $$
--
--   The value of information enters the threshold rule through the coefficient $\Phi_i(\mathbf s)$.
--
--   **Formalization Note** The identity holds also when a child state is infeasible, where $V^*$ is $0$ and its coefficient vanishes.
--
--   Differences from the source:
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - generalization: the Mendelian prior (5) → an arbitrary mass function on $\{0,1,2\}^{\mathcal I}$; reason: the argument does not use the pedigree and p.11 says priors incorporate all prior information; (5) is the special case given by the theorem eq_5_mendelian_prior
--   - encoding: a state as a partition $\{s_0,s_1,s_2\}$ of the tested individuals, state space $\mathcal S=\{\mathbf s:\exists g\in\mathcal G(\mathbf s)\}$ → `State I := I → Option (Fin 3)`, with `Feasible` meaning $\mathbb P(G\in\mathcal G(\mathbf s))>0$; reason: same objects when $\mathcal G$ is the support of the prior; the family is a `Fintype`, possibly empty
--   - encoding: $\alpha_i(\mathbf s)$ is a ratio with denominator $\mathbb P_i(\mathbf s)$ → $\alpha_i(\mathbf s)=0$ when the denominator is $0$; reason: the page leaves this case undefined; every use of $\alpha_i$ is then multiplied by $0$
--   - encoding: $V^*$ as the maximum of (3), an expectation over sample paths with absorbing state $\Delta$ and action $C$, undefined at infeasible states → `Vstar`: the maximum over the finite type `Policy I` of the posterior average of a rolled-out return, with no $\Delta$ and no $C$; $V^*=0$ at infeasible states; reason: given $G=g$ and the rule the path is determined, so the two expectations agree; the infeasible children enter only with coefficient $0$
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), (EC.2), p.ec2

import Mathlib
import Definitions.Def_FamilyGenTest_Pmax

namespace FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- (EC.2) (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), p.ec2):
`Eᵢ[V*(S′) | s] = Φᵢ(s)ℙᵢ(s) + V*(s₀ ∪ {i})`. -/
theorem ec_2 (R : Rewards I) (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    ∑ γ, marginal μ s i γ * Vstar R μ (test s i γ)
      = Phi R μ s i * risk μ s i + Vstar R μ (test s i 0) := by sorry

end FamilyGenTest
