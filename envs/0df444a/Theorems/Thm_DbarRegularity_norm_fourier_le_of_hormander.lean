-- Prove2me | Theorems.Thm_DbarRegularity_norm_fourier_le_of_hormander
-- name    : DbarRegularity.norm_fourier_le_of_hormander
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:47:25.110597+00:00
-- url     : https://prove2.me/theorems/0410f2b0-b001-4e7b-83aa-876719e5a49a
-- title:
--   Uniform Fourier bound for integrable kernels with size, Hörmander and cancellation conditions
-- statement:
--   Let $d\ge1$. There is a constant $C\ge0$, depending only on $d$, with the following property. Let $K\in L^1(\mathbb{R}^d)$ be complex-valued, and let $B\in\mathbb{R}$ and $B_1\ge0$ be such that
--   $$|K(x)|\le B|x|^{-d}\ (x\ne0),\qquad\int_{|x|\ge2|y|}|K(x-y)-K(x)|\,dx\le B_1\ (y\ne0),\qquad\int_{|x|<r}K(x)\,dx=0\ (r>0).$$
--   Then its Fourier transform $\hat K(\xi)=\int_{\mathbb{R}^d}e^{-2\pi i\langle x,\xi\rangle}K(x)\,dx$ satisfies
--   $$|\hat K(\xi)|\le C\,(B+B_1)\qquad\text{for all }\xi\in\mathbb{R}^d .$$
--
--   The bound depends on $K$ only through $B$ and $B_1$.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume`; $\hat K$ is Mathlib's `𝓕 K` (kernel $e^{-2\pi i\langle x,\xi\rangle}$). The second condition is a lower Lebesgue integral `∫⁻` of `‖·‖ₑ` bounded by `ENNReal.ofReal B₁`; the third is a Bochner integral over the open ball `ball 0 r`. $C$ is chosen before $K$, $B$, $B_1$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, p. 35

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace DbarRegularity

open MeasureTheory Set Metric FourierTransform
open scoped ENNReal Real RealInnerProductSpace

/-- The Fourier transform of an integrable kernel with `|K(x)| ≤ B |x|^{-d}`, Hörmander constant
`B₁` and vanishing integrals over all balls `B(0, r)` is bounded by `C (B + B₁)`, with `C`
depending only on `d`. -/
theorem norm_fourier_le_of_hormander {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ) (B B₁ : ℝ), 0 ≤ B₁ →
      Integrable K volume →
      (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d) →
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B₁) →
      (∀ r : ℝ, 0 < r → ∫ x in ball 0 r, K x = 0) →
      ∀ ξ, ‖𝓕 K ξ‖ ≤ C * (B + B₁) := by sorry

end DbarRegularity
