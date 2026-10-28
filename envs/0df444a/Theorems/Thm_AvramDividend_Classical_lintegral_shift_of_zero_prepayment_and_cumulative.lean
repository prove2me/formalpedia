-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_shift_of_zero_prepayment_and_cumulative
-- name    : AvramDividend.Classical.lintegral_shift_of_zero_prepayment_and_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:40:10.565601+00:00
-- url     : https://prove2.me/theorems/4c4f17d9-d33e-4f48-917d-53442677e8e6
-- title:
--   Translate full discounted reward from no prepayment and cumulative shifted dividend increments
-- statement:
--   Zero Stieltjes mass up to a stopping time and equality of cumulative post-stopping interval dividends imply exact equality of every measurable nonnegative weighted payout integral with the translated future integral. This is the deterministic whole-reward transport used before strong-Markov factorisation.
-- source:
--   Direct reusable weighted Stieltjes pathwise bridge for W-free dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380. Imports proof of cumulative-to-measure translation 50431279-23d0-42be-b261-421a5476921e, whose compile verdict must be Proved before this is submitted.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_measure_eq_translated_of_zero_prepayment_and_cumulative

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.lintegral_shift_of_zero_prepayment_and_cumulative
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ] (u : ℝ)
    (hμzero : μ (Set.Iic u) = 0)
    (hνzero : ν (Set.Iic (0 : ℝ)) = 0)
    (hcum : ∀ t : ℝ, 0 ≤ t →
      μ (Set.Ioc u (u + t)) = ν (Set.Ioc (0 : ℝ) t))
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t : ℝ, f t ∂μ) =
      ∫⁻ t : ℝ, f (u + t) ∂ν := by
  sorry
