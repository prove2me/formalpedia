-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
-- name    : AvramDividend.Classical.avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:25:07.028731+00:00
-- url     : https://prove2.me/theorems/6189fbe3-5c93-4e70-840a-579156a95097
-- title:
--   Earlier original negative Lévy marked cell count real-valued is strongly measurable in any later right-continuous physical-grid filtration
-- statement:
--   For the genuine original spectrally negative Lévy process, the toReal negative marked-jump count in the physical cell (s,t] with Borel marks B is measurable at its actual right endpoint t. Hence it is strongly measurable at any later u in the right-continuous original filtration. This provides the past-factor measurability required to combine stopped predictable coefficients with future conditionally-centred full negative mark increments.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    StronglyMeasurable[𝓕.rightCont u] (fun ω : Ω =>
      (((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) r ≠ 0}).map
        (fun r : ℝ≥0 => (r,
          X.X r ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) r)))
        (Ioc s t ×ˢ B)).toReal) := by sorry
