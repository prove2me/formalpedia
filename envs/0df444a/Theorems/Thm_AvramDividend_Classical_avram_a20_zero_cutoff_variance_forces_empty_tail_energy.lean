-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_zero_cutoff_variance_forces_empty_tail_energy
-- name    : AvramDividend.Classical.avram_a20_zero_cutoff_variance_forces_empty_tail_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:55:24.303384+00:00
-- url     : https://prove2.me/theorems/8b2c8d40-d562-4339-983d-41ed001be799
-- title:
--   Exact cutoff-zero obstruction to the displayed small-jump variance identity
-- statement:
--   The platform's existing displayed variance formula for the original compensated small-band jump at cutoff n is incompatible with the true cutoff-zero process unless the quadratic Levy mass over negative unit marks vanishes. At n zero the physical compensated band is identically zero by a Proved source theorem, whereas the displayed formula assigns the opposite omitted-tail energy. Formalise this source-faithful necessary condition, without asserting an invalid universal moment identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_zero_cutoff_variance_forces_empty_tail_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hVar : ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) :
    (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂X.ν) = 0 := by sorry
