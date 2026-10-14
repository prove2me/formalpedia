-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_doubleTruncation_le
-- name    : DbarRegularity.eLpNorm_doubleTruncation_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:57:06.813744+00:00
-- url     : https://prove2.me/theorems/353c77aa-0706-42b3-bf20-0bb7177336c5
-- title:
--   Uniform L^p bounds for doubly truncated singular integrals on L^1 ∩ L^p
-- statement:
--   Let $d\ge1$, $B\in\mathbb{R}$, and let $K:\mathbb{R}^d\to\mathbb{C}$ be measurable with
--   $$|K(x)|\le B|x|^{-d}\ (x\ne0),\qquad \int_{|x|\ge2|y|}|K(x-y)-K(x)|\,dx\le B\ (y\ne0),\qquad \int_{R_1<|x|<R_2}K(x)\,dx=0\ (0<R_1<R_2).$$
--   For $0<\varepsilon$ and $0<R$ let $K_{\varepsilon,R}=K\,\mathbf 1_{\{\varepsilon\le|x|<R\}}$. Let $1<p<\infty$. Then there is a constant $A$, independent of $\varepsilon$, $R$ and $f$, such that
--   $$\Big\|\int_{\mathbb{R}^d}K_{\varepsilon,R}(\cdot-y)f(y)\,dy\Big\|_p\le A\|f\|_p$$
--   for all $\varepsilon>0$, $R>0$ and all $f\in L^1(\mathbb{R}^d)\cap L^p(\mathbb{R}^d)$.
--
--   This is the uniform $L^p$ boundedness of the doubly truncated singular integrals of a kernel satisfying Stein's conditions (18)–(19).
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume`. $K_{\varepsilon,R}$ is `{x | ‖x‖ < R}.indicator ({x | ε ≤ ‖x‖}.indicator K)`; the convolution is the Bochner integral `∫ y, K_{ε,R} (x - y) * f y`. The second condition is a lower Lebesgue integral `∫⁻` bounded by `ENNReal.ofReal B`. `A : ℝ≥0` is chosen before $\varepsilon$, $R$, $f$; the exponent is `ENNReal.ofReal p`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, p. 35

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- For a kernel satisfying Stein's conditions (18)–(19), the operators
`f ↦ ∫ K_{ε,R}(x - y) f(y) dy` with the doubly truncated kernel `K_{ε,R} = K 1_{ε ≤ |x| < R}` are
bounded on `L^1 ∩ L^p`, `1 < p < ∞`, uniformly in `0 < ε` and `0 < R`. -/
theorem eLpNorm_doubleTruncation_le {d : ℕ} (hd : 0 < d) (K : EuclideanSpace ℝ (Fin d) → ℂ)
    (B : ℝ) (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK2 : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ ε R : ℝ, 0 < ε → 0 < R → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
      Integrable f volume → MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (fun x => ∫ y, {x | ‖x‖ < R}.indicator ({x | ε ≤ ‖x‖}.indicator K) (x - y) * f y)
          (ENNReal.ofReal p) volume ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
