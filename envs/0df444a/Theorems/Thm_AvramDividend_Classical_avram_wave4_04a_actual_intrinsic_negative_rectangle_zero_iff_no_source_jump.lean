-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:56:28.162152+00:00
-- url     : https://prove2.me/theorems/4087af7c-0c1d-4a4d-9a78-b349256366d0
-- title:
--   Original Lévy intrinsic negative-jump rectangle has zero count exactly when the actual path has no jumps
-- statement:
--   For every original sample path of the actual spectrally negative Lévy source, the intrinsic source counting measure of the time-negative-mark rectangle (s,t] × (-∞,0) is zero if and only if the true left-limit jump mark vanishes at every time in (s,t]. No exceptional set, replacement probability space, or constructed Poisson process; all original-path counts and marks are retained. This is the exact pathwise bridge needed to transfer a source no-jump exponential law to the counting measure.
-- source:
--   The canonically Proved original-path rectangular count identity f6336d40-2d19-444f-bacd-83724316de67 and every-positive-time true source jump nonpositivity e95fe5bc-c756-43ca-82d7-acab7078e2eb. The count is Set.encard of actual negative jump times; because all nonzero source marks are strictly negative, this encard equals zero iff there is no nonzero jump in the interval.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) = 0 ↔
      ∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by sorry
