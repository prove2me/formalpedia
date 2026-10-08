-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_partition_bracket
-- name    : AvramDividend.Classical.discounted_dividendMeasure_Ico_partition_bracket
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T08:25:51.047014+00:00
-- url     : https://prove2.me/theorems/9d5942b7-2dba-4812-8b28-f7b1b45f9dad
-- title:
--   Exact two-sided Darboux bracket for the full discounted Stieltjes dividend integral on an interval
-- statement:
--   Under a nonnegative discount rate q, the discounted Lebesgue–Stieltjes dividend integral on any [a,b) against an actual dividend strategy is bracketed below by exp(−qb)*(D_b−D_a) and above by exp(−qa)*(D_b−D_a). The proof joins the independently developed endpoint-discount bounds. It provides the precise interval-by-interval Riemann–Stieltjes upper and lower sums for continuous and jump payments, a useful foundation for integration-by-parts, partition limits and more general stochastic dividend verification.
-- source:
--   Children discounted_dividendMeasure_Ico_ge_end_weighted_increment and discounted_dividendMeasure_Ico_le_start_weighted_increment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_dividendMeasure_Ico_partition_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * (b : ℝ))) * (D b ω - D a ω)) ≤
      (∫⁻ s in Ico (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ∧
      (∫⁻ s in Ico (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ))) * (D b ω - D a ω)) := by sorry
