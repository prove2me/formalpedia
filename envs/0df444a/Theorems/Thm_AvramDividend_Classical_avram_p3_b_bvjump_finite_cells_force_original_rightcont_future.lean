-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_finite_cells_force_original_rightcont_future
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_finite_cells_force_original_rightcont_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:25:51.851116+00:00
-- url     : https://prove2.me/theorems/b0272810-33ac-4838-bd0a-33232552e4bf
-- title:
--   Original finite predictable rectangle mass equality forces rightCont strict-future mass equality
-- statement:
--   Assume the actual original marked-measure occupation M and physical predictable Lévy product N agree on all finite (s,t] cylinders for original-filtration past events. Deduce exactly the strict-future equality for every rightCont past event required by the original P3 stopped BV compensated expectation helper. The other required structural facts are proven by standalone accepted P3-B helper theorems: predictable measurability, finite-to-infinite extension, cofinal clock and right-continuous transfer. This is explicitly conditional on the P2 source finite-rectangle compensation hypothesis; no independent Poisson measure or compensator axiom is introduced.
-- source:
--   Prove2Me accepted P3-B helper theorems; Mathlib Filtration.rightCont_eq and Measure.measure_iUnion; Avram Proposition 4(i), Eq. 5.13.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_cofinal_strict_future_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_rightcont_past_measurable_at_later_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_finite_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_finite_rectangles_to_original_future
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_rightcont_future_of_decreasing_later_tails
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_finite_cells_force_original_rightcont_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _
       (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRect : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        N ((Ioc s t ×ˢ A) ×ˢ B))
    (i : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont i] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    M ((Ioi i ×ˢ A) ×ˢ B) =
      N ((Ioi i ×ˢ A) ×ˢ B) := by sorry
