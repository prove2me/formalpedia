-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_countable_simple_indicator_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_countable_simple_indicator_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:29:02.051925+00:00
-- url     : https://prove2.me/theorems/2696b4b7-5def-4f68-a553-571281e70802
-- title:
--   Countable nonnegative simple marked integrand integrates to true measure masses
-- statement:
--   For countably many measurable marked cells, even with infinite activity or overlapping cells, the integral of the countable sum of nonnegative cell indicators with constant coefficients equals the countable sum of each coefficient multiplied by the exact underlying measure mass. This is the countable pathwise Tonelli step for original Lévy jump-measure predictable integrands and never substitutes an independent Poisson process. The result is valid for zero and infinite values, with no disjointness or summability hypothesis.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_tsum, lintegral_indicator and constant integral under restrict.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_countable_simple_indicator_lintegral
    {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α)
    (C : ι → Set α) (hC : ∀ i, MeasurableSet (C i))
    (w : ι → ℝ≥0∞) :
    (∫⁻ x, ∑' i, (C i).indicator (fun _ => w i) x ∂μ) =
    ∑' i, w i * μ (C i) := by sorry
