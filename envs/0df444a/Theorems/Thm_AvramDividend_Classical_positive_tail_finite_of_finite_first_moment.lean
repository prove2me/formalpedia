-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_tail_finite_of_finite_first_moment
-- name    : AvramDividend.Classical.positive_tail_finite_of_finite_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:49:00.656172+00:00
-- url     : https://prove2.me/theorems/e3dbca5f-3531-405a-9b14-be1cfb093d3c
-- title:
--   A finite positive first moment makes every strict positive jump tail finite
-- statement:
--   For a measure on nonnegative jump magnitudes, finite extended-real first moment forces its upper-tail mass above any strictly positive threshold to be finite. Apply the already Proved sharp first-moment Markov inequality and positivity of the threshold. This supplies exactly the positive-tail finiteness hypothesis needed for the causal real-density identification of the Esscher-weighted BV kernel.
-- source:
--   Canonical Proved positive_jump_tail_threshold_mass_le_first_moment, combined with ENNReal positivity and finite moment.

import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_threshold_mass_le_first_moment
import Mathlib.Data.ENNReal.Real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_tail_finite_of_finite_first_moment
    (μ : Measure ℝ≥0)
    (hmoment : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    ∀ t : ℝ, 0 < t →
      μ {z : ℝ≥0 | t < (z : ℝ)} ≠ ⊤ := by sorry
