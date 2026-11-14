-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_omitted_negative_tail_integrable_centered_20261113
-- name    : AvramDividend.Classical.avram_a21_original_omitted_negative_tail_integrable_centered_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:22:45.92721+00:00
-- url     : https://prove2.me/theorems/6b0d1770-1ee6-42d4-adcb-624d808ba722
-- title:
--   Original omitted negative compensated tail has finite first moment and mean zero
-- statement:
--   The genuinely OMITTED compensated negative mark tail Rn-R on the original Lévy sample space is L1 and has zero mean. Its L1 component is already independently proved from source L2; mean zero follows from the Proved finite-cutoff residual mean-zero theorem and the same-source Gaussian limit centring theorem, using Bochner integral subtraction.
-- source:
--   Proved all original finite-cutoff Gaussian residual L1 centered 6942df41; direct L1 omitted tail 0cb3d170; source Gaussian-limit L1 centered 5bdde16f (currently Open contingent on same-source companion).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_omitted_negative_tail_integrable_centered_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) P ∧
      (∫ ω, avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω ∂P) = 0 := by sorry
