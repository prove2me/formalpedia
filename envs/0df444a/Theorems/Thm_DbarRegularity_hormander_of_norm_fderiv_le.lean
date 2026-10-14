-- Prove2me | Theorems.Thm_DbarRegularity_hormander_of_norm_fderiv_le
-- name    : DbarRegularity.hormander_of_norm_fderiv_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T14:54:39.566337+00:00
-- url     : https://prove2.me/theorems/70aeffeb-02c1-4d01-b8e5-0ce768fdc37e
-- title:
--   A gradient bound $|\nabla K(x)|\le B|x|^{-d-1}$ implies the Hörmander condition with constant $C_dB$
-- statement:
--   Let $d\ge0$. There is a constant $C$, depending only on $d$, with the following property. Let $B\in\mathbb R$ and let $K:\mathbb R^d\to\mathbb C$ be continuously differentiable on $\mathbb R^d\setminus\{0\}$ with
--   $$|\nabla K(x)|\le\frac{B}{|x|^{d+1}}\qquad(x\ne0).$$
--   Then for every $y\neq0$
--   $$\int_{\{x:\ |x|\ge 2|y|\}}\big|K(x-y)-K(x)\big|\,dx\;\le\;C\,B .$$
--
--   The conclusion is the Hörmander integral condition on a convolution kernel, with a constant that depends only on the dimension and on the gradient bound $B$ (not on any other norm of $K$).
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure. "$C^1$ off the origin" is `ContDiffOn ℝ 1 K {0}ᶜ`, and $|\nabla K(x)|$ is the operator norm of the real Fréchet derivative `fderiv ℝ K x`. The integral is the lower Lebesgue integral `∫⁻` of `‖K (x - y) - K x‖ₑ` over `{x | 2 * ‖y‖ ≤ ‖x‖}`, bounded by `ENNReal.ofReal (C * B)`; `C` is chosen before `B` and `K`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal ContDiff

/-- If `K : ℝ^d → ℂ` is `C¹` off the origin with `|∇K(x)| ≤ B / |x|^{d+1}`, then
`∫_{|x| ≥ 2|y|} |K(x - y) - K(x)| dx ≤ C B` for every `y ≠ 0`, with `C` depending only on `d`. -/
theorem hormander_of_norm_fderiv_le (d : ℕ) :
    ∃ C : ℝ, ∀ (B : ℝ) (K : EuclideanSpace ℝ (Fin d) → ℂ),
      ContDiffOn ℝ 1 K {0}ᶜ →
      (∀ x, x ≠ 0 → ‖fderiv ℝ K x‖ ≤ B / ‖x‖ ^ (d + 1)) →
      ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal (C * B) := by sorry

end DbarRegularity
