-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_eq_C_4
-- name    : ConsumerUtilityApprox.UnitDemand.eq_C_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:55:22.502202+00:00
-- url     : https://prove2.me/theorems/ec46971d-f2be-4ebd-a50f-1ca29b32756b
-- title:
--   Appendix C.3, (C.4) — bisection gives 2b − 2γ ≤ U(M^free_b) ≤ 2b and the free-lottery guarantee up to additive γ
-- statement:
--   Work in normalized units: a buyer with independent values $V_j\sim G_j$, $0<\mathbb E[V_j]<\infty$, $\sum_j\mathbb E[V_j]\le1$, demand weights $\lambda\ge0$, and $\gamma\in(0,1]$. Let $f(h)=U(M^{\mathrm{free}}_h)$ be the expected utility of the free lotteries $\ell_j(h)$, and run the bisection on $[a,b]=[0,1]$ (test $f(c)>2c$ at the midpoint) for $k=\lceil\log_2(1/\gamma)\rceil$ steps, so $b-a\le\gamma$. Then $b>0$,
--   $$2b-2\gamma\le U(M^{\mathrm{free}}_b)\le 2b,$$
--   the number $k$ of evaluations satisfies $k\le 1+\log_2(1/\gamma)$, and for every BIC, IR single-buyer unit-demand mechanism $C$ with nonnegative payments and deletion loss $D$,
--   $$U(M^{\mathrm{free}}_b)-\sum_j\lambda_jq^{\mathrm{alloc}}_j(M^{\mathrm{free}}_b)\ \ge\ \frac{U(C)-D}{2}-\sum_j\lambda_jq^{\mathrm{alloc}}_j(C)-\gamma.\qquad(C.4)$$
--   This is the computable version of the free-lottery bound (5.5), whether or not $U(M^{\mathrm{free}}_h)=2h$ has a root.
--
--   Differences from the source:
--   - encoding: values in R_+, laws F_j, items 1..m → ℝ≥0, ProbabilityMeasure ℝ≥0, Fin m; product law vecLaw; reason: Lean conventions for the same objects
--   - reading: expectations E[x_j(V)], E[u(V)] of a single-buyer mechanism (rules tacitly measurable) → IsTruthfulIRNPT includes Borel measurability of x and p; reason: the standing convention without which the source's expectations are undefined
--   - generalization: normalized units of Appendix C.4 (Σ_{i,j} E[V_ij] = 1, λ ∈ [0,1]^m) → Σ_j E[V_j] ≤ 1 for the buyer and λ ≥ 0, no upper bound on λ; reason: the C.3 argument uses only U(M^free_1) ≤ 2, which Σ_j E[V_j] ≤ 1 gives; the normalized setting is a special case
--   - encoding: after O(1 + log(1/γ)) exact evaluations → bisectSteps γ = ⌈log₂(1/γ)⌉ evaluations, with bisectSteps γ ≤ 1 + log₂(1/γ); reason: explicit constant for O(·); one evaluation of U(M^free_c) per step
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 43, Appendix C.3, (C.4) (continues on p. 44)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem eq_C_4 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (hnorm : ∑ j, mean (G j) ≤ 1)
    (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    let f : ℝ → ℝ := fun h => utility (vecLaw G) (freeLotteryMech (lotteryProb lam h)).reduced
    let b : ℝ := (bisect f γ).2
    let Mb : Mechanism (Fin m) := (freeLotteryMech (lotteryProb lam b)).reduced
    0 < b ∧ 2 * b - 2 * γ ≤ f b ∧ f b ≤ 2 * b ∧
      (bisectSteps γ : ℝ) ≤ 1 + Real.logb 2 (1 / γ) ∧
      ∀ C : Mechanism (Fin m), IsTruthfulIRNPT C → IsUnitDemand C →
        (utility (vecLaw G) C - totalDeletionLoss (vecLaw G) C) / 2
            - ∑ j, lam j * qAlloc (vecLaw G) C j - γ
          ≤ utility (vecLaw G) Mb - ∑ j, lam j * qAlloc (vecLaw G) Mb j := by sorry

end ConsumerUtilityApprox.UnitDemand
