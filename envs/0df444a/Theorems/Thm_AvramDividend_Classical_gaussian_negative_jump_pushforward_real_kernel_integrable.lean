-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_real_kernel_integrable
-- name    : AvramDividend.Classical.gaussian_negative_jump_pushforward_real_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T12:23:57.86599+00:00
-- url     : https://prove2.me/theorems/8d5f189d-e378-4f10-8e34-362b17f22f93
-- title:
--   Real Gaussian Volterra kernel from negative Lévy jumps is integrable
-- statement:
--   If a spectrally negative Lévy jump measure has no nonnegative jumps and satisfies the truncated-square condition on negative jump sizes, then its positive jump-magnitude pushforward admits the global real Gaussian double-tail Esscher kernel in L1(0,∞). The proof combines the Proved sigma-finite sign-pushforward theorem, Proved truncated-square pushforward moment, and Proved global real-kernel integrability theorem. This transports the analytic kernel hypothesis back to the native signed Lévy measure used by the original process.
-- source:
--   gaussian_negative_jump_pushforward_sigmaFinite, gaussian_levy_square_integrable_neg_pushforward, gaussian_double_tail_real_kernel_integrable

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_negative_jump_pushforward_real_kernel_integrable (ν : Measure ℝ) (hν : ν (Ici (0 : ℝ)) = 0) (hlevy : (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) (φ : ℝ) (hφ : 0 < φ) : IntegrableOn (fun t : ℝ => (∫⁻ z : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂(ν.map (fun y : ℝ => -y))).toReal) (Ioi (0 : ℝ)) volume := by sorry
