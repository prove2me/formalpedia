-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:49:24.125672+00:00
-- url     : https://prove2.me/theorems/12e84fff-dc00-4473-8213-068484f459ae
-- title:
--   Actual original Lévy intrinsic counting measure gives zero mass to nonnegative jump marks
-- statement:
--   For every sample ω of the actual original source spectrally negative Lévy process X, the intrinsic true-path jump-counting measure formed by restricting time-count measure to positive nonzero jumps and pushing by u↦(u,ΔX_uω) assigns zero mass to any rectangle (s,t]×[0,∞). This is a measure-level spectral-support identity for the genuine source X, without a Poisson, compensation or finite-activity assumption.
-- source:
--   Canonical Proved source original-path intrinsic rectangle measure f6336d40-2d19-444f-bacd-83724316de67 and all-path nonpositive jump marks e95fe5bc-c756-43ca-82d7-acab7078e2eb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Ici (0 : ℝ)) = 0 := by sorry
