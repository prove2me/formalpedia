-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise29_original_zero_cutoff_gaussian_core_martingale
-- name    : AvramDividend.Classical.avram_anoise29_original_zero_cutoff_gaussian_core_martingale
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T10:08:34.606896+00:00
-- url     : https://prove2.me/theorems/6bbd3299-8e85-4f09-ab3f-313bc0ed5c4d
-- title:
--   Original Gaussian residual zero-cutoff Lévy martingale
-- statement:
--   For an original finite-activity spectrally negative Lévy process under Standing, the intrinsic zero-cutoff residual is an integrable martingale for the original right-continuous filtration. This is the zero-cutoff source component of the Gaussian residual cutoff martingale.
-- source:
--   Source residual is X minus c t minus its actual finite large negative jump sum, with no auxiliary Brownian identification. Standing includes Integrable(X 1).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise29_original_zero_cutoff_gaussian_core_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    (∀ t : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) P) ∧
    (∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont s) P
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ω =
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω) := by sorry
