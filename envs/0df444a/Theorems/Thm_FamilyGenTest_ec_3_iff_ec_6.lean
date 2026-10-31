-- Prove2me | Theorems.Thm_FamilyGenTest_ec_3_iff_ec_6
-- name    : FamilyGenTest.ec_3_iff_ec_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:27.070122+00:00
-- url     : https://prove2.me/theorems/c6437636-37d8-4547-8cd4-99f4e0b246cd
-- title:
--   (EC.3)–(EC.6) — testing $i$ beats stopping iff the quadratic inequality holds
-- statement:
--   Let $\mathbf s$ be feasible and $i$ untested in $\mathbf s$. The advantage of testing $i$ over stopping is the net gain function at the risk,
--   $$
--   Q^*_i(\mathbf s)-\sum_{l\in\mathcal I\setminus\mathbf s}\bar r_l(\mathbb P_l(\mathbf s))=\mathrm{gap}_i(\mathbf s)(\mathbb P_i(\mathbf s)),
--   $$
--   and therefore (EC.3), $Q^*_i(\mathbf s)\ge\sum_{l\in\mathcal I\setminus\mathbf s}\bar r_l(\mathbb P_l(\mathbf s))$, holds if and only if (EC.6) does:
--   $$
--   -r_i^\delta\mathbb P_i(\mathbf s)^2+\bigl(r_i^\delta+d_i-c_i^f+\Phi_i(\mathbf s)\bigr)\mathbb P_i(\mathbf s)-c_i^s+V^*(\mathbf s_0\cup\{i\})-\sum_{l\in\mathcal I\setminus\mathbf s:\,l\ne i}\bar r_l(\mathbb P_l(\mathbf s))\ge0.
--   $$
--
--   This reduces the stopping decision for $i$ to a quadratic inequality in $\mathbb P_i(\mathbf s)$.
--
--   Differences from the source:
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - generalization: the Mendelian prior (5) → an arbitrary mass function on $\{0,1,2\}^{\mathcal I}$; reason: the argument does not use the pedigree and p.11 says priors incorporate all prior information; (5) is the special case given by the theorem eq_5_mendelian_prior
--   - encoding: a state as a partition $\{s_0,s_1,s_2\}$ of the tested individuals, state space $\mathcal S=\{\mathbf s:\exists g\in\mathcal G(\mathbf s)\}$ → `State I := I → Option (Fin 3)`, with `Feasible` meaning $\mathbb P(G\in\mathcal G(\mathbf s))>0$; reason: same objects when $\mathcal G$ is the support of the prior; the family is a `Fintype`, possibly empty
--   - encoding: $r_i(\mathbb P_i(\mathbf S'))$ with Definition 3 and Assumption 1 → `testedReward`: $r_i^0(0)$ at result $0$, $r_i^1(1)$ at results $1,2$; reason: after a test the belief is the true carrier status, which is what Assumption 1 and Definition 3 give
--   - encoding: $V^*$ as the maximum of (3), an expectation over sample paths with absorbing state $\Delta$ and action $C$, undefined at infeasible states → `Vstar`: the maximum over the finite type `Policy I` of the posterior average of a rolled-out return, with no $\Delta$ and no $C$; $V^*=0$ at infeasible states; reason: given $G=g$ and the rule the path is determined, so the two expectations agree; the infeasible children enter only with coefficient $0$
--   - generalization: the reward assumptions of §4 → arbitrary real rewards and costs; reason: the statement does not depend on them, and every instance of the source is covered
--   - encoding: $\alpha_i(\mathbf s)$ is a ratio with denominator $\mathbb P_i(\mathbf s)$ → $\alpha_i(\mathbf s)=0$ when the denominator is $0$; reason: the page leaves this case undefined; every use of $\alpha_i$ is then multiplied by $0$
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), (EC.3)–(EC.6), pp.ec2–ec3

import Mathlib
import Definitions.Def_FamilyGenTest_Pmax

namespace FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- (EC.3)–(EC.6) (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023),
pp.ec2–ec3): `Eᵢ[rᵢ(ℙᵢ(S′)) − cᵢ(s) + V*(S′) | s] − ∑_{l ∈ I \ s} r̄_l(ℙ_l(s))` is the left side of
(EC.6) at `ℙᵢ(s)`, so (EC.3) holds iff (EC.6) holds. -/
theorem ec_3_iff_ec_6 (R : Rewards I) (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    Qstar R μ s i - stopValue R μ s = gap R μ s i (risk μ s i) ∧
    (stopValue R μ s ≤ Qstar R μ s i ↔
      0 ≤ -rdelta R i * risk μ s i ^ 2
          + (rdelta R i + censoring R i - R.cf i + Phi R μ s i) * risk μ s i
          - R.cs i + Vstar R μ (test s i 0)
          - ∑ l ∈ (untested s).erase i, rbar R l (risk μ s l)) := by sorry

end FamilyGenTest
