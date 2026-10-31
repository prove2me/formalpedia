-- Prove2me | Theorems.Thm_FamilyGenTest_ec_1
-- name    : FamilyGenTest.ec_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:56.020399+00:00
-- url     : https://prove2.me/theorems/5100f00f-3dd9-4635-8048-de6c97f331c9
-- title:
--   (EC.1) — the net benefit of testing as a quadratic in the risk
-- statement:
--   Let $\mathbf s$ be feasible and $i$ untested in $\mathbf s$. Then
--   $$
--   \mathbb E_i[r_i(\mathbb P_i(\mathbf S'))\mid\mathbf s]-c_i(\mathbf s)-\bar r_i(\mathbb P_i(\mathbf s))=-r_i^\delta\,\mathbb P_i(\mathbf s)^2+(r_i^\delta+d_i-c_i^f)\,\mathbb P_i(\mathbf s)-c_i^s.
--   $$
--
--   This is the one-person net benefit of testing, the source of the two-sided form of the rule.
--
--   Differences from the source:
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - generalization: the Mendelian prior (5) → an arbitrary mass function on $\{0,1,2\}^{\mathcal I}$; reason: the argument does not use the pedigree and p.11 says priors incorporate all prior information; (5) is the special case given by the theorem eq_5_mendelian_prior
--   - encoding: a state as a partition $\{s_0,s_1,s_2\}$ of the tested individuals, state space $\mathcal S=\{\mathbf s:\exists g\in\mathcal G(\mathbf s)\}$ → `State I := I → Option (Fin 3)`, with `Feasible` meaning $\mathbb P(G\in\mathcal G(\mathbf s))>0$; reason: same objects when $\mathcal G$ is the support of the prior; the family is a `Fintype`, possibly empty
--   - encoding: $r_i(\mathbb P_i(\mathbf S'))$ with Definition 3 and Assumption 1 → `testedReward`: $r_i^0(0)$ at result $0$, $r_i^1(1)$ at results $1,2$; reason: after a test the belief is the true carrier status, which is what Assumption 1 and Definition 3 give
--   - generalization: the reward assumptions of §4 (Assumptions 1–4) → arbitrary real rewards and costs; reason: the identity is algebraic in the data and does not use them; every instance of the source is covered
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), (EC.1), p.ec2

import Mathlib
import Definitions.Def_FamilyGenTest_Rewards

namespace FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- (EC.1) (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), p.ec2):
`Eᵢ[rᵢ(ℙᵢ(S′)) | s] − cᵢ(s) − r̄ᵢ(ℙᵢ(s)) = −rᵢ^δ ℙᵢ(s)² + (rᵢ^δ + dᵢ − cᵢᶠ) ℙᵢ(s) − cᵢˢ`. -/
theorem ec_1 (R : Rewards I) (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    (∑ γ, marginal μ s i γ * testedReward R i γ) - cost R μ s i - rbar R i (risk μ s i)
      = -rdelta R i * risk μ s i ^ 2 + (rdelta R i + censoring R i - R.cf i) * risk μ s i
        - R.cs i := by sorry

end FamilyGenTest
