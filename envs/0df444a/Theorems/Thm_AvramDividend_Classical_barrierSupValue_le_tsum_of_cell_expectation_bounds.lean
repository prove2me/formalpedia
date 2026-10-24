-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_tsum_of_cell_expectation_bounds
-- name    : AvramDividend.Classical.barrierSupValue_le_tsum_of_cell_expectation_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:59:50.69498+00:00
-- url     : https://prove2.me/theorems/1364ae36-55b9-4bf1-bedb-d1d542032c50
-- title:
--   Stopped barrier reward bounded by any cellwise upper-budget series
-- statement:
--   For an actual reflected barrier dividend strategy, any summable nonnegative extended-real upper budget controlling each expected discounted stopped Stieltjes payout also bounds the total dividend value. This complements the lower budget result and isolates the stochastic first-record upper-survival estimates needed by the renewal upper-bound theorem.
-- source:
--   Consequence of Proved unconditional stopped Stieltjes reward expectation partition and monotonicity of ENNReal infinite sums.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_sum_expected_partition_rewards_unconditional

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_le_tsum_of_cell_expectation_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0)
    (f : ℕ → ℝ≥0∞)
    (hf : ∀ i : ℕ,
      (∫⁻ ω, (
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) ≤ f i) :
    barrierSupValue X a q ≤ (∑' i, f i) := by sorry
