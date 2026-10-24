-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_antitone_positive
-- name    : AvramDividend.Classical.gaussian_double_tail_real_kernel_antitone_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:16:53.701401+00:00
-- url     : https://prove2.me/theorems/bd75eadf-39ed-4bef-83be-15299898e29d
-- title:
--   Antitonicity of the finite real Gaussian Esscher double-tail kernel
-- statement:
--   Under the Gaussian Lévy integrability hypothesis, the finite real-valued representation of the Esscher double-tail kernel decreases on strictly positive times. This transfers the already proved extended-nonnegative-valued monotonicity using finiteness and the monotonicity of the toReal conversion.
-- source:
--   Application of proved Gaussian double-tail finiteness and antitonicity results, preparatory to a local convolution-power majorant.

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_antitone
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_finite_positive

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_real_kernel_antitone_positive
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    AntitoneOn
      (fun t : ℝ => (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ).toReal)
      (Ioi (0 : ℝ)) := by sorry
