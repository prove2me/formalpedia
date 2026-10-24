-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_weighted_double_tail_antitone
-- name    : AvramDividend.Classical.gaussian_weighted_double_tail_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:06:16.451087+00:00
-- url     : https://prove2.me/theorems/45cf5176-aac2-4723-aa06-dbde5eefe472
-- title:
--   The exponentially damped Gaussian Esscher double-tail envelope is antitone
-- statement:
--   Let μ be a sigma-finite or s-finite Lévy jump magnitude measure with finite truncated quadratic moment and φ>0. Its real Esscher double-tail kernel K(t)=∫_{z>t}(z−t)e^(−φz)μ(dz) is finite, nonnegative and antitone at positive times. For every real β and nonnegative exponential damping rate w, the weighted envelope exp(−wt)(|β|+K(t)) is also antitone on positive times. Combine the remotely verified real double-tail antitonicity theorem with the previously Proved general weighted positive-kernel antitonicity theorem. This supplies the exact kernel hypothesis for Gaussian Volterra convolution-power bounds.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_antitone_positive
import Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_weighted_double_tail_antitone
    (μ : Measure ℝ) [SFinite μ] (φ β w : ℝ)
    (hφ : 0 < φ) (hw : 0 ≤ w)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    AntitoneOn (fun t : ℝ =>
      Real.exp (-w * t) *
        (|β| + (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ).toReal))
      (Ioi (0 : ℝ)) := by sorry
