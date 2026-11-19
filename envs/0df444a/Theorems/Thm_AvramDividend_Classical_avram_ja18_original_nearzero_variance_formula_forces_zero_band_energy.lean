-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_nearzero_variance_formula_forces_zero_band_energy
-- name    : AvramDividend.Classical.avram_ja18_original_nearzero_variance_formula_forces_zero_band_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:10:08.519192+00:00
-- url     : https://prove2.me/theorems/1e5561c5-11f6-4556-a6de-4614c4b9f778
-- title:
--   Original intrinsic retained-smallband cutoff refutes nearzero square formula unless smallmark energy vanishes
-- statement:
--   The actual original Levy source small-band compensated term is built from retained marks in (-1,-1/(n+1)], and at n=0 its interval is empty. Therefore the incorrect universal formula assigning its second moment the nearzero-marks variance in (-1/(n+1),0) forces the total smallmark quadratic Levy energy over (-1,0) to vanish. This is a necessary condition for Open ja21 nearzero moment equation and exposes its retained-vs-omitted-band specification mismatch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_nearzero_variance_formula_forces_zero_band_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hNear : ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω,
        (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2 ∂P) =
        (t : ℝ) *
          (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) :
    (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂X.ν) = 0 := by sorry
