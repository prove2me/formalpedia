-- Prove2me | Theorems.Thm_FamousTheorems_two_pi_i_inv_smul_circleintegral_sub_inv_smul_of_differentiable_on_off_countable
-- name    : FamousTheorems.two_pi_i_inv_smul_circleintegral_sub_inv_smul_of_differentiable_on_off_countable
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:08.915901+00:00
-- url     : https://prove2.me/theorems/9575cb7e-ddf2-45c5-b4a2-2c42bb40b6ba
-- title:
--   Cauchy's integral formula
-- statement:
--   **Cauchy's integral formula.** For a function differentiable on a disc (off a countable exceptional set) and continuous on its closure, the value at an interior point is recovered from the boundary values: $$f(w) = \frac{1}{2\pi i}\oint_{|z-c|=R} \frac{f(z)}{z-w}\,dz.$$ A holomorphic function is determined on the whole disc by its restriction to the boundary circle — an extraordinarily strong rigidity with no real-analytic counterpart. Everything characteristic of complex analysis follows: differentiating under the integral shows a once-differentiable function is infinitely differentiable and analytic; the mean value property and maximum modulus principle follow by taking $w = c$; Liouville's theorem and hence the fundamental theorem of algebra come from estimating the integral on large circles. The countable exceptional set in this version is a genuine strengthening: it allows isolated bad points, which is what makes the formula applicable in the presence of removable singularities. Cauchy developed the formula in the 1820s and 30s. **Formalization note.** `circleIntegral` is the integral over a parametrised circle; the hypothesis is differentiability on the open ball minus a countable set, plus continuity on the closed ball. The result is Mathlib's `Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem two_pi_i_inv_smul_circleintegral_sub_inv_smul_of_differentiable_on_off_countable :
    ∀ {E : Type u_1} 
    [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {R : ℝ} {c w : ℂ} {f : ℂ → E} {s : Set ℂ}, 
    s.Countable → 
    w ∈ Metric.ball c R → 
    ContinuousOn f (Metric.closedBall c R) → 
    (∀ x ∈ Metric.ball c R \ s, DifferentiableAt ℂ f x) → 
    (2 * ↑Real.pi * Complex.I)⁻¹ • ∮ (z : ℂ) in C(c, R), (z - w)⁻¹ • f z = f w := by sorry

end FamousTheorems
