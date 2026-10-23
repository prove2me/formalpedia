-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_global_kernel_integrable
-- name    : AvramDividend.Classical.gaussian_double_tail_global_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T12:05:49.835397+00:00
-- url     : https://prove2.me/theorems/3a119d60-726a-47bc-a9a3-2f95bc2cbe07
-- title:
--   Global integrability of the Gaussian Esscher double-tail Volterra kernel
-- statement:
--   The total mass over all positive time and jump magnitudes of the Gaussian Esscher double-tail kernel is finite under the ordinary Lévy truncated-square condition. Apply the published Gaussian Tonelli theorem at Laplace parameter zero, calculate each positive-magnitude triangular atom's area exp(−φz)z²/2, and use the proved global damped quadratic moment. For nonpositive z the triangular indicator vanishes. This removes the main global kernel integrability obstruction from the Gaussian Volterra representation.
-- source:
--   Proved gaussian_double_tail_tonelli, gaussian_double_tail_atom_full_lintegral, gaussian_esscher_damped_quadratic_integrable

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_global_kernel_integrable (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ) (hlevy : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) : (∫⁻ t : ℝ, ∫⁻ z : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ ∂volume) < ⊤ := by sorry
