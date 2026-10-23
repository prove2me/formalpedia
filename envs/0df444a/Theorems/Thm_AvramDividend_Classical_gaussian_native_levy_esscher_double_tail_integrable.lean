-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_native_levy_esscher_double_tail_integrable
-- name    : AvramDividend.Classical.gaussian_native_levy_esscher_double_tail_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T14:35:04.107332+00:00
-- url     : https://prove2.me/theorems/2d44c23e-3249-49f5-a17c-81132661426a
-- title:
--   Native Lévy Gaussian Esscher double-tail kernel is globally L1
-- statement:
--   For a spectrally negative Lévy process, the native quadratic truncation condition on its signed jump measure yields global real integrability of the Esscher-damped positive-magnitude double-tail kernel. Restrict the native Lévy moment to negative jumps and use spectral negativity to invoke the proved pushforward-integrability theorem.
-- source:
--   Direct consequence of the native SpectrallyNegativeLevy fields ν_Ici and ν_integrable and proved gaussian_negative_jump_pushforward_real_kernel_integrable.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_real_kernel_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_native_levy_esscher_double_tail_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ : ℝ) (hφ : 0 < φ) :
    IntegrableOn (fun t : ℝ =>
      (∫⁻ z : ℝ,
        if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
        else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal)
      (Ioi (0 : ℝ)) volume := by sorry
