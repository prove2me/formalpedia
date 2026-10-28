-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_clock_section_probability_transfer
-- name    : AvramDividend.Classical.avram_ws01e_b_independent_clock_section_probability_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:09:14.12107+00:00
-- url     : https://prove2.me/theorems/d1f793c0-df84-468c-89b7-20ccea41fdb0
-- title:
--   Independent random clock preserves equality of path-section event probabilities
-- statement:
--   Given finite or σ-finite path and clock measures P and Q, if two measurable events in the path-clock product have the same P-probability in every fixed-clock section, then they have equal probabilities under the independent product measure P×Q. This is a source-faithful Tonelli transfer step for passing fixed-horizon strict Lévy drawdown/minimum reversal to random independent horizons.
-- source:
--   Pinned Mathlib Measure.prod_apply_symm and lintegral_congr_ae; mathematical Fubini/Tonelli disintegration for independent random horizons.

import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set

/-- Equal measurable path-section probabilities transfer through an independent clock. -/

theorem AvramDividend.Classical.avram_ws01e_b_independent_clock_section_probability_transfer
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) [SFinite P]
    (Q : Measure Θ) [SFinite Q]
    (A B : Set (Ω × Θ))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSections : ∀ η : Θ,
      P ((fun ω : Ω => (ω, η)) ⁻¹' A) =
      P ((fun ω : Ω => (ω, η)) ⁻¹' B)) :
    (P.prod Q) A = (P.prod Q) B := by sorry
