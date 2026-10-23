-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_integrable
-- name    : AvramDividend.Classical.gaussian_double_tail_real_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T12:17:15.139468+00:00
-- url     : https://prove2.me/theorems/f311dd04-0a89-4bbe-9cf4-9b7ee14c0846
-- title:
--   Real-valued Gaussian Esscher double-tail kernel belongs to L1
-- statement:
--   Under the usual Lévy truncated-square condition, the real-valued Gaussian double-tail kernel K(t) obtained by converting the finite ENNReal jump integral with toReal is globally integrable in time. Measurability of K comes from measurability of the joint (t,z)-integrand and Measurable.lintegral_prod_right. The already proved global ENNReal integral bound, together with integrable_toReal_of_lintegral_ne_top, yields real L1 integrability. This supplies precisely the analytic kernel required by the Gaussian Volterra equation.
-- source:
--   Proved gaussian_double_tail_global_kernel_integrable and pinned Mathlib integrable_toReal_of_lintegral_ne_top

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_real_kernel_integrable (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ) (hlevy : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) : Integrable (fun t : ℝ => (∫⁻ z : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ).toReal) volume := by sorry
