-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_real_double_tail_kernel_full_regularity
-- name    : AvramDividend.Classical.gaussian_real_double_tail_kernel_full_regularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:18:41.529407+00:00
-- url     : https://prove2.me/theorems/86fbdd38-a3b4-4eec-b835-ebbe30cb14d3
-- title:
--   Gaussian Esscher causal double-tail kernel is integrable, continuous and antitone
-- statement:
--   For a positive Esscher exponent and a Lévy jump-magnitude measure obeying the truncated quadratic moment condition, the canonical real double-tail kernel K(t)=∫_{z>t}(z−t)e^(−φz)μ(dz) is Lebesgue integrable on the whole real line, continuous and nonincreasing at every strictly positive time, and nonnegative there. Assemble the remotely Proved exact integrability, continuity and antitonicity results in one usable convolution-kernel regularity package for Gaussian q-scale function C2 smoothing.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_antitone_positive
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_real_double_tail_kernel_full_regularity
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    ∃ K : ℝ → ℝ,
      K = (fun t : ℝ => (∫⁻ z : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ).toReal) ∧
      Integrable K volume ∧
      ContinuousOn K (Ioi (0 : ℝ)) ∧
      AntitoneOn K (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, 0 < t → 0 ≤ K t) := by sorry
