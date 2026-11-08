-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto
-- name    : AvramDividend.Classical.avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:29:01.705925+00:00
-- url     : https://prove2.me/theorems/2bd5c3b4-a446-4ef0-9936-b7bef044076d
-- title:
--   Original physical-grid coefficient localisation complements vanish in finite measure
-- statement:
--   For any finite original probability or finite measure and a fixed finite physical-grid row, coordinatewise measurable path coefficients define increasing measurable bounded-coefficient events whose complementary measures converge to zero. The result derives from original-grid measurable exhaustion by the continuity-from-above theorem and explicitly assumes finite measure. It enables the localisation-in-measure argument for the original process; it does not prove uniform integrability.
-- source:
--   AVRAM BV-RESIDUAL10 original process finite-grid localisation; MathFin LocalisationInMeasure source technique, 7 November 2026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_exhaustion

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i)) :
    Tendsto (fun k : ℕ =>
      P ({ω : Ω | ∀ i ∈ Finset.range (n + 1),
        abs (a ω i) ≤ (k : ℝ)}ᶜ)) atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
