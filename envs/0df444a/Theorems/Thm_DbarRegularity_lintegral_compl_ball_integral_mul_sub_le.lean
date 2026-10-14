-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_compl_ball_integral_mul_sub_le
-- name    : DbarRegularity.lintegral_compl_ball_integral_mul_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:26:52.561639+00:00
-- url     : https://prove2.me/theorems/499783a1-66ad-410d-bff2-d8f68d418759
-- title:
--   Hörmander kernels map mean-zero functions supported in $\bar B(c,r)$ to $L^1$ off $B(c,2r)$ with norm $\le B\|b\|_1$
-- statement:
--   Let $d\ge0$, $B\in\mathbb R$, and let $K:\mathbb R^d\to\mathbb C$ be measurable and satisfy the Hörmander condition
--   $$\int_{\{x:\ |x|\ge2|y|\}}|K(x-y)-K(x)|\,dx\le B\qquad(y\ne0).$$
--   Let $b\in L^1(\mathbb R^d)$ with $\int b=0$, vanishing outside the closed ball $\bar B(c,r)$. Then
--   $$\int_{\mathbb R^d\setminus B(c,2r)}\Big|\int_{\mathbb R^d}K(x-y)\,b(y)\,dy\Big|\,dx\;\le\;B\,\|b\|_{L^1}.$$
--
--   This is the off-support estimate for convolution with a Hörmander kernel acting on a single mean-zero "atom", the basic ingredient in weak-type $(1,1)$ bounds for singular integrals.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. The Hörmander condition is the lower integral `∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B`. "Vanishing outside $\bar B(c,r)$" is `∀ x, b x ≠ 0 → x ∈ closedBall c r`. The inner integral is the Bochner integral (set to $0$ where not integrable), the outer one is `∫⁻` of `‖·‖ₑ` over `(ball c (2 * r))ᶜ`, and the bound is `ENNReal.ofReal B * eLpNorm b 1 volume`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, pp. 29–31

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal

/-- Off the doubled ball, convolution with a kernel satisfying the Hörmander condition maps a
mean-zero function supported in `closedBall c r` into `L¹` with norm at most `B ‖b‖₁`. -/
theorem lintegral_compl_ball_integral_mul_sub_le {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK : AEStronglyMeasurable K volume) (B : ℝ)
    (hH : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (b : EuclideanSpace ℝ (Fin d) → ℂ) (hb : Integrable b volume) (hb0 : ∫ x, b x = 0)
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (hsupp : ∀ x, b x ≠ 0 → x ∈ closedBall c r) :
    ∫⁻ x in (ball c (2 * r))ᶜ, ‖∫ y, K (x - y) * b y‖ₑ ≤
      ENNReal.ofReal B * eLpNorm b 1 volume := by sorry

end DbarRegularity
