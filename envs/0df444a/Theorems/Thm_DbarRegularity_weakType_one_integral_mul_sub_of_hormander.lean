-- Prove2me | Theorems.Thm_DbarRegularity_weakType_one_integral_mul_sub_of_hormander
-- name    : DbarRegularity.weakType_one_integral_mul_sub_of_hormander
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:53:07.45238+00:00
-- url     : https://prove2.me/theorems/60103e60-2c6e-4a1e-936d-45970f55f3ae
-- title:
--   Weak type $(1,1)$ for convolution with an $L^2$-bounded Hörmander kernel on $\mathbb R^d$
-- statement:
--   Let $d\ge1$. There is a constant $C\ge0$, depending only on $d$, with the following property. Let $K\in L^2(\mathbb R^d)$ be complex valued and let $B_1,B_2\ge0$. Suppose that
--
--   * $K$ satisfies the Hörmander condition with constant $B_1$:
--   $$\int_{\{x:\ |x|\ge2|y|\}}|K(x-y)-K(x)|\,dx\le B_1\qquad(y\ne0);$$
--   * convolution with $K$ is bounded on $L^2$ with norm at most $B_2$: $\|K*g\|_{L^2}\le B_2\|g\|_{L^2}$ for every $g\in L^2(\mathbb R^d)$.
--
--   Then $f\mapsto K*f$, where $K*f(x)=\int K(x-y)f(y)\,dy$, is of weak type $(1,1)$: for every $f\in L^1(\mathbb R^d)$ and every $\alpha>0$,
--   $$\big|\{x:\ |K*f(x)|>\alpha\}\big|\;\le\;\frac{C\,(1+B_1+B_2^2)}{\alpha}\,\|f\|_{L^1}.$$
--
--   This is the weak-type $(1,1)$ estimate for singular convolution operators. Together with the $L^2$ bound it gives the $L^p$ bounds for $1<p\le2$ by interpolation.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`, and $d\ge1$ is `0 < d`. The constants $C,B_1,B_2,\alpha$ are in `ℝ≥0`, and $\alpha>0$. The Hörmander condition is the lower integral `∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁`. The $L^2$ bound is stated with `eLpNorm · 2 volume`. $K*f(x)$ is the Bochner integral `∫ y, K (x - y) * f y` (set to $0$ where not integrable). The conclusion reads `volume {x | α < ‖∫ y, K (x - y) * f y‖ₑ} ≤ ↑(C * (1 + B₁ + B₂ ^ 2)) / α * eLpNorm f 1 volume`, which is the weak-type form used by the published Marcinkiewicz interpolation theorem.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, Theorem 1, pp. 29–31

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- Weak type `(1, 1)` for convolution with an `L²` kernel `K` on `ℝ^d` that satisfies the
Hörmander condition with constant `B₁` and is bounded on `L²` with norm `B₂`:
`|{|K * f| > α}| ≤ C (1 + B₁ + B₂²) ‖f‖₁ / α`, with `C` depending only on `d`. -/
theorem weakType_one_integral_mul_sub_of_hormander {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ≥0, ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ), MemLp K 2 volume → ∀ B₁ B₂ : ℝ≥0,
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁) →
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (x - y) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) →
      ∀ f, MemLp f 1 volume → ∀ α : ℝ≥0, 0 < α →
        volume {x | (α : ℝ≥0∞) < ‖∫ y, K (x - y) * f y‖ₑ} ≤
          ((C * (1 + B₁ + B₂ ^ 2) : ℝ≥0) : ℝ≥0∞) / α * eLpNorm f 1 volume := by sorry

end DbarRegularity
