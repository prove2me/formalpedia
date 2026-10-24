-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_tsum_of_cell_expectation_bounds
-- name    : AvramDividend.Classical.barrierSupValue_ge_tsum_of_cell_expectation_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:59:16.413644+00:00
-- url     : https://prove2.me/theorems/499f7b08-2e7d-4e08-9128-36d4e7a6f3ae
-- title:
--   Stopped barrier reward dominates any cellwise lower-budget series
-- statement:
--   For the actual reflected barrier dividend value, take any monotone cofinal partition of nonnegative payment time. If a nonnegative extended-real budget for each cell is bounded by that cell's expected discounted stopped Stieltjes payout, then the total renewal budget is bounded by the full reflected barrier value. This is a reusable countable-monotonicity interface that isolates the genuinely stochastic first-record survival estimates still to be proved.
-- source:
--   Consequence of the Proved unconditional stopped Stieltjes reward expectation partition and monotonicity of ENNReal infinite sums.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_sum_expected_partition_rewards_unconditional

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_ge_tsum_of_cell_expectation_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0)
    (f : ℕ → ℝ≥0∞)
    (hf : ∀ i : ℕ, f i ≤
      (∫⁻ ω, (
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P)) :
    (∑' i, f i) ≤ barrierSupValue X a q := by sorry
