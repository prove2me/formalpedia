-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_integral_mul_sub_le_of_hormander
-- name    : DbarRegularity.eLpNorm_integral_mul_sub_le_of_hormander
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:03:56.919185+00:00
-- url     : https://prove2.me/theorems/0ca70f6d-e4b5-4cdd-accf-aeb28e1d0c3a
-- title:
--   $L^p$ bounds, $1<p<\infty$, for convolution with an $L^2$-bounded Hörmander kernel on $\mathbb R^d$, uniform in the kernel
-- statement:
--   Let $d\ge1$, $1<p<\infty$ and $B_1,B_2\ge0$. There is a constant $A\ge0$, depending only on $d,p,B_1,B_2$, with the following property. Let $K\in L^2(\mathbb R^d)$ be complex valued, and suppose that
--
--   * $K$ satisfies the Hörmander condition with constant $B_1$:
--   $$\int_{\{x:\ |x|\ge2|y|\}}|K(x-y)-K(x)|\,dx\le B_1\qquad(y\ne0);$$
--   * convolution with $K$ is bounded on $L^2$ with norm at most $B_2$: $\|K*g\|_{L^2}\le B_2\|g\|_{L^2}$ for every $g\in L^2(\mathbb R^d)$.
--
--   Then for every $f\in L^1(\mathbb R^d)\cap L^p(\mathbb R^d)$,
--   $$\|K*f\|_{L^p}\le A\,\|f\|_{L^p},\qquad K*f(x)=\int K(x-y)f(y)\,dy .$$
--
--   This is the $L^p$ theory of singular convolution operators with Hörmander kernels, for the whole range $1<p<\infty$ and with a constant uniform over all kernels satisfying the two bounds.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`, and $d\ge1$ is `0 < d`. $p$ is real, and $L^p$ norms are `eLpNorm · (ENNReal.ofReal p) volume`. The constants $A,B_1,B_2$ are in `ℝ≥0`. The Hörmander condition is the lower integral `∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁`. $f\in L^1\cap L^p$ is `Integrable f volume` and `MemLp f (ENNReal.ofReal p) volume`. $K*f(x)$ is the Bochner integral `∫ y, K (x - y) * f y` (set to $0$ where not integrable). The quantifiers are ordered $\exists A\ \forall K\ \forall f$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, Theorem 1, pp. 29–31

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal NNReal

/-- `L^p` bound, `1 < p < ∞`, on `L¹ ∩ L^p` for convolution with an `L²` kernel `K` on `ℝ^d` that
satisfies the Hörmander condition with constant `B₁` and is bounded on `L²` with norm `B₂`; the
constant depends only on `d`, `p`, `B₁`, `B₂`. -/
theorem eLpNorm_integral_mul_sub_le_of_hormander {d : ℕ} (hd : 0 < d) (p : ℝ) (hp : 1 < p)
    (B₁ B₂ : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ K : EuclideanSpace ℝ (Fin d) → ℂ, MemLp K 2 volume →
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁) →
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (x - y) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) →
      ∀ f, Integrable f volume → MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal p) volume ≤
          A * eLpNorm f (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
