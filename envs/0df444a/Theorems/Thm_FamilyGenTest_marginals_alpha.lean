-- Prove2me | Theorems.Thm_FamilyGenTest_marginals_alpha
-- name    : FamilyGenTest.marginals_alpha
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:15.78445+00:00
-- url     : https://prove2.me/theorems/3d757742-c9e9-44b5-8d89-27e47c22c80b
-- title:
--   Proof of Theorem 1, first display — the three marginals in terms of $\mathbb P_i$ and $\alpha_i$
-- statement:
--   Let $\mathbf s$ be feasible and $i$ untested in $\mathbf s$. Then
--   $$
--   \mathbb P(g_i=0\mid\mathbf s)=1-\mathbb P_i(\mathbf s),\quad \mathbb P(g_i=1\mid\mathbf s)=\alpha_i(\mathbf s)\mathbb P_i(\mathbf s),\quad \mathbb P(g_i=2\mid\mathbf s)=(1-\alpha_i(\mathbf s))\mathbb P_i(\mathbf s).
--   $$
--
--   This writes the law of the next test result through the single number $\mathbb P_i(\mathbf s)$ and the split $\alpha_i(\mathbf s)$ among carriers.
--
--   Differences from the source:
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - generalization: the Mendelian prior (5) → an arbitrary mass function on $\{0,1,2\}^{\mathcal I}$; reason: the argument does not use the pedigree and p.11 says priors incorporate all prior information; (5) is the special case given by the theorem eq_5_mendelian_prior
--   - encoding: a state as a partition $\{s_0,s_1,s_2\}$ of the tested individuals, state space $\mathcal S=\{\mathbf s:\exists g\in\mathcal G(\mathbf s)\}$ → `State I := I → Option (Fin 3)`, with `Feasible` meaning $\mathbb P(G\in\mathcal G(\mathbf s))>0$; reason: same objects when $\mathcal G$ is the support of the prior; the family is a `Fintype`, possibly empty
--   - encoding: $\alpha_i(\mathbf s)$ is a ratio with denominator $\mathbb P_i(\mathbf s)$ → $\alpha_i(\mathbf s)=0$ when the denominator is $0$; reason: the page leaves this case undefined; every use of $\alpha_i$ is then multiplied by $0$
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), Proof of Theorem 1, p.ec2

import Mathlib
import Definitions.Def_FamilyGenTest_risk

namespace FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Proof of Theorem 1, first display (Adelman & Wang, Optimal Genetic Testing of Families,
SSRN 4624694 (Jan 24 2023), p.ec2): `ℙ(gᵢ = 0 | s) = 1 − ℙᵢ(s)`, `ℙ(gᵢ = 1 | s) = αᵢ(s)ℙᵢ(s)`,
`ℙ(gᵢ = 2 | s) = (1 − αᵢ(s))ℙᵢ(s)`. -/
theorem marginals_alpha (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    marginal μ s i 0 = 1 - risk μ s i ∧
    marginal μ s i 1 = alpha μ s i * risk μ s i ∧
    marginal μ s i 2 = (1 - alpha μ s i) * risk μ s i := by sorry

end FamilyGenTest
