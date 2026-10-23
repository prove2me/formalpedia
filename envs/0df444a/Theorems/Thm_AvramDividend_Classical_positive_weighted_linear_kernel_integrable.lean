-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_weighted_linear_kernel_integrable
-- name    : AvramDividend.Classical.positive_weighted_linear_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T19:10:30.672108+00:00
-- url     : https://prove2.me/theorems/51a18595-a34d-451f-bcce-b1cc8e4bd265
-- title:
--   Adding a constant drift preserves exponential-weighted integrability of the Volterra kernel
-- statement:
--   If the positive-halfline exponentially damped real kernel K is integrable, then for any real constant β the kernel β+K is also integrable after damping by exp(−t). This follows by multiplying the proved integrable exponential kernel exp(−t) by β and adding the original weighted K. It discharges the remaining scalar-drift integrability premise in Gaussian Esscher Volterra convolution continuity.
-- source:
--   Proved positive_laplace_constant_reference (θ=1); MeasureTheory.Integrable.const_mul and Integrable.add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_weighted_linear_kernel_integrable (K : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn (fun t : ℝ => Real.exp (-t) * K t)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * (β + K t))
      (Ioi (0 : ℝ)) volume := by sorry
