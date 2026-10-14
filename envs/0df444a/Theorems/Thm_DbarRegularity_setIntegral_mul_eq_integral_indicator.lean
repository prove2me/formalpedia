-- Prove2me | Theorems.Thm_DbarRegularity_setIntegral_mul_eq_integral_indicator
-- name    : DbarRegularity.setIntegral_mul_eq_integral_indicator
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T18:07:28.610981+00:00
-- url     : https://prove2.me/theorems/a227133e-c67a-498d-af41-b122e524bcfe
-- title:
--   Truncated singular integrals as convolutions with the truncated kernel
-- statement:
--   Let $d\ge0$, $K,f:\mathbb{R}^d\to\mathbb{C}$, $\varepsilon\in\mathbb{R}$ and $x\in\mathbb{R}^d$, and let $K_\varepsilon=K\,\mathbf 1_{\{|y|\ge\varepsilon\}}$. Then
--   $$\int_{|y|\ge\varepsilon}f(x-y)K(y)\,dy=\int_{\mathbb{R}^d}K_\varepsilon(x-y)\,f(y)\,dy .$$
--
--   The truncated singular integral $T_\varepsilon f(x)$ is thus the convolution of $f$ with the truncated kernel $K_\varepsilon$, evaluated at $x$.
--
--   **Formalization Note.** Both sides are Bochner integrals with respect to Lebesgue measure `volume` on `EuclideanSpace ℝ (Fin d)`, the left one over the set `{y | ε ≤ ‖y‖}`; the identity holds with no integrability assumptions (both sides are $0$ when the integrands are not integrable). $K_\varepsilon$ is `{y | ε ≤ ‖y‖}.indicator K`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, p. 35

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set

/-- The truncated singular integral as a convolution with the truncated kernel. -/
theorem setIntegral_mul_eq_integral_indicator {d : ℕ} (K f : EuclideanSpace ℝ (Fin d) → ℂ)
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y =
      ∫ y, {y | ε ≤ ‖y‖}.indicator K (x - y) * f y := by sorry

end DbarRegularity
