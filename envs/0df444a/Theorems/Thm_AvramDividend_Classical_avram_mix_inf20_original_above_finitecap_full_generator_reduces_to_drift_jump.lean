-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
-- name    : AvramDividend.Classical.avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:36:03.089186+00:00
-- url     : https://prove2.me/theorems/771f63e9-90e4-4cc3-9211-3591999af622
-- title:
--   Genuine original spectrally negative Lévy above finite-cap caplinear generator equals triplet drift plus true truncated jump generator integral
-- statement:
--   Source-faithful original spectrally negative Levy full extended generator identity for a caplinear potential V at every reserve y strictly above the finite barrier b. The Gaussian Hessian term is exactly zero, derivative one, and the original generator becomes triplet drift X.c plus the exact actual truncated compensated negative-jump integral SpectrallyNegativeLevy.generatorIntegrand, matching the original source definition word for word. This uses the already Proved upper affine derivative+curvature theorem 90e5b7db. It is an essential corrected finite-cap original physical Itô source reduction: the Gaussian channel vanishes on the upper strip and jump sign can be controlled by genuine original mark bounds without assuming raw w above cap is smooth. No integrability is claimed unless separately verified.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (b y : ℝ) (hy : b < y) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ b then w t else w b + (t - b)
    X.generator V y = X.c +
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand V y z ∂X.ν) := by sorry
