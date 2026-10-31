-- Prove2me | Theorems.Thm_FamilyGenTest_eq_12
-- name    : FamilyGenTest.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:58.56935+00:00
-- url     : https://prove2.me/theorems/ff425eaf-0bef-4c09-b2e4-02d6ff62e1c5
-- title:
--   Eq. (12) — the expected reward of a test
-- statement:
--   Let $\mathbf s$ be feasible and $i$ untested in $\mathbf s$. The expected reward of testing $i$ is
--   $$
--   \mathbb E_i[r_i(\mathbb P_i(\mathbf S'))\mid\mathbf s]=(1-\mathbb P_i(\mathbf s))\,r_i^0(0)+\mathbb P_i(\mathbf s)\,r_i^1(1),
--   $$
--   the left side being the average of the reward of $i$ over the test result.
--
--   The expected reward of a test is thus linear in the risk, in contrast with the quadratic no-testing reward (11).
--
--   Differences from the source:
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - generalization: the Mendelian prior (5) → an arbitrary mass function on $\{0,1,2\}^{\mathcal I}$; reason: the argument does not use the pedigree and p.11 says priors incorporate all prior information; (5) is the special case given by the theorem eq_5_mendelian_prior
--   - encoding: a state as a partition $\{s_0,s_1,s_2\}$ of the tested individuals, state space $\mathcal S=\{\mathbf s:\exists g\in\mathcal G(\mathbf s)\}$ → `State I := I → Option (Fin 3)`, with `Feasible` meaning $\mathbb P(G\in\mathcal G(\mathbf s))>0$; reason: same objects when $\mathcal G$ is the support of the prior; the family is a `Fintype`, possibly empty
--   - encoding: $r_i(\mathbb P_i(\mathbf S'))$ with Definition 3 and Assumption 1 → `testedReward`: $r_i^0(0)$ at result $0$, $r_i^1(1)$ at results $1,2$; reason: after a test the belief is the true carrier status, which is what Assumption 1 and Definition 3 give
--   - generalization: the reward assumptions of §4 (Assumptions 1–4) → arbitrary real rewards and costs; reason: the identity is algebraic in the data and does not use them; every instance of the source is covered
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), (12), p.16

import Mathlib
import Definitions.Def_FamilyGenTest_Rewards

namespace FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Eq. (12) (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023),
p.16): `Eᵢ[rᵢ(ℙᵢ(S′)) | s] = (1 − ℙᵢ(s)) rᵢ⁰(0) + ℙᵢ(s) rᵢ¹(1)`. -/
theorem eq_12 (R : Rewards I) (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    ∑ γ, marginal μ s i γ * testedReward R i γ
      = (1 - risk μ s i) * R.r0at0 i + risk μ s i * R.r1at1 i := by sorry

end FamilyGenTest
