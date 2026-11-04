-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_arbitrary_borel_rate_of_negative_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_arbitrary_borel_rate_of_negative_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:28:45.683215+00:00
-- url     : https://prove2.me/theorems/9d64d756-a13e-49df-a778-14a847d90b05
-- title:
--   Original arbitrary-Borel marked rate follows from the exact negative-restriction rate
-- statement:
--   For the unchanged original Lévy process, suppose the unconditional exact marked jump-rate equality is established only on B∩(-∞,0). Then the arbitrary Borel B equality follows from already proved pathwise negative support of literal jumps and negative support of the original Lévy measure, including infinite expected counts. The hypothesis is explicit, leaving no unproved child-theorem import.
-- source:
--   Source-faithful conditional transport abstracting the existing 859bf7be sketch; relies exclusively on Proved 56a5b5da and c324380a and leaves the missing negative rate as a visible assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_arbitrary_borel_rate_of_negative_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hnegRate :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
