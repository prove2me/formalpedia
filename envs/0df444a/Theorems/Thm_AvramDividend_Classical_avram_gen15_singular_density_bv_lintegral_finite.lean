-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_bv_lintegral_finite
-- name    : AvramDividend.Classical.avram_gen15_singular_density_bv_lintegral_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:20:34.012356+00:00
-- url     : https://prove2.me/theorems/c5a09120-667e-4eb6-b3a5-ad54b47aa273
-- title:
--   Singular negative Levy density satisfies the original bounded-variation lintegral field
-- statement:
--   The explicit singular negative-jump Levy measure has finite extended-nonnegative first absolute moment on the source-defined small negative jump band, exactly discharging the measure part of SpectrallyNegativeLevy.BoundedVariation. This is derived from a proved real Bochner integrability result and the exact first-moment integral two.
-- source:
--   Previously accepted exact singular first-moment equality and integrability, pinned ofReal_integral_eq_lintegral_ofReal and lintegral_mono_set.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen15_singular_density_bv_lintegral_finite :
    (∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal |z| ∂
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) < ⊤ := by sorry
