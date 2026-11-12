-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_zero_cutoff_increment_mean_zero
-- name    : AvramDividend.Classical.avram_ja18g_original_zero_cutoff_increment_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:36:02.925296+00:00
-- url     : https://prove2.me/theorems/da3bb1d8-bf53-4804-9997-c7761f8bff9b
-- title:
--   Physical zero-cutoff residual increments have zero mean
-- statement:
--   Under Standing and finite negative-jump intensity, the original fixed-time residual R0(t)=X(t)-ct-original-large-jump-sum has centred increments. Combine original X Laplace-exponent first derivative, finite negative-jump first moment and the original Campbell identity; no auxiliary Gaussian process.
-- source:
--   J-A18 original-filtration Gaussian zero-cutoff martingale split

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_zero_cutoff_increment_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ s t : ℝ≥0, s ≤ t →
      (∫ ω,
        (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
         avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω) ∂P) = 0 := by sorry
