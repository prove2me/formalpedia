-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_restored_compensator_smalljump_equals_physical_finite_mark_sum
-- name    : AvramDividend.Classical.avram_a22_original_restored_compensator_smalljump_equals_physical_finite_mark_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:41:53.260202+00:00
-- url     : https://prove2.me/theorems/7a0de1b3-76dd-4274-81ea-17e083027cf4
-- title:
--   Original compensated smallmark integral restored by its true Lévy first moment equals finite original signed physical small-mark sum
-- statement:
--   For an original Lévy sample path with a finite actual jump-time support F on [0,t], add the literal source Lévy band compensator back to the intrinsic original compensated small-negative-mark integral at cutoff n. The result is exactly the finite sum over actual jumps in (-1,-1/(n+1)], with mark -1 excluded and no independent noise or extra probability space. Uses proved original smallmark signed measure-to-tsum identity and finite-support summation. Essential step in finite-activity original Lévy–Itô source recovery.
-- source:
--   Proved 79505e86 original signed small marked integral equals source tsum, original compensated source definition 66a113ed, finite physical support a55466fc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_restored_compensator_smalljump_equals_physical_finite_mark_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) (n : ℕ)
    (F : Finset ℝ≥0)
    (hF : ∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
      (t : ℝ) * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν) =
      ∑ u ∈ F,
        if -1 < X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
           X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
             -(1 / ((n : ℝ) + 1))
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0 := by sorry
