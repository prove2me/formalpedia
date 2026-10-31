-- Prove2me | Theorems.Thm_AubinLipschitz_pseudoLipschitz_of_contingent_bound
-- name    : AubinLipschitz.pseudoLipschitz_of_contingent_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:53.895223+00:00
-- url     : https://prove2.me/theorems/91c48689-780f-4247-a592-d60a28302396
-- title:
--   §3, Theorem 2 — the quantitative pseudo-Lipschitz estimate with explicit constants
-- statement:
--   Let $F$ be a closed set-valued map from a Banach space $X$ to a Banach space $Y$, and $(x_0,y_0)\in\operatorname{graph}(F)$. Assume there are $\alpha\in[0,1[$, $\eta>0$ and $c>0$ such that for all $(x,y)\in\operatorname{graph}(F)$ with $\|x-x_0\|+\|y-y_0\|\le\eta$ and all $v\in Y$ there exist $u\in X$, $w\in Y$ with
--
--   $$
--   v\in DF(x,y)(u)+w,\qquad\|u\|\le c\|v\|,\qquad\|w\|\le\alpha\|v\|.
--   $$
--
--   Set
--
--   $$
--   r:=\frac{\eta(1-\alpha)}{3(1+\alpha+c)},\qquad \ell:=\frac{c+2\alpha}{1-\alpha},
--   $$
--
--   and $F_0^{-1}(y):=F^{-1}(y)\cap(x_0+\ell rB)$, $F_1^{-1}(y):=F^{-1}(y)\cap(x_0+3\ell rB)$. Then
--
--   1. $F_0^{-1}(y)\neq\emptyset$ for all $y$ in the open ball $y_0+r\mathring B$;
--   2. $\underline d\big(F_0^{-1}(y_1),F_1^{-1}(y_2)\big)\le\ell\|y_1-y_2\|$ for all $y_1,y_2$ in that open ball.
--
--   So $F^{-1}$ is pseudo-Lipschitz around $(y_0,x_0)$, with explicit neighbourhoods and constant.
--
--   Differences from the source: none.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Theorem 2, pp.23–24

import Mathlib
import Definitions.Def_AubinLipschitz_contingentDeriv
import Definitions.Def_AubinLipschitz_graphOf
import Definitions.Def_AubinLipschitz_invMap

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Theorem 2, pp.23–24: let `F` be a closed set-valued map between Banach spaces
and `(x₀, y₀) ∈ graph(F)`. Assume constants `α ∈ [0, 1[`, `η > 0`, `c > 0` such that for all
`(x, y) ∈ graph(F)` with `‖x − x₀‖ + ‖y − y₀‖ ≤ η` and all `v` there are `u`, `w` with
`v ∈ DF(x, y)(u) + w`, `‖u‖ ≤ c‖v‖`, `‖w‖ ≤ α‖v‖`. With `r = η(1 − α)/(3(1 + α + c))` and
`ℓ = (c + 2α)/(1 − α)`, setting `F₀⁻¹(y) = F⁻¹(y) ∩ (x₀ + ℓ r B)` and
`F₁⁻¹(y) = F⁻¹(y) ∩ (x₀ + 3 ℓ r B)`:
(8)i `F₀⁻¹(y) ≠ ∅` for all `y ∈ y₀ + r B̊`, and
(8)ii `d(F₀⁻¹(y₁), F₁⁻¹(y₂)) ≤ ℓ ‖y₁ − y₂‖` for all `y₁, y₂ ∈ y₀ + r B̊`.

**Formalization Note** The balls around `x₀` are closed and the balls around `y₀` open, as
printed. The hypothesis uses the sum `‖x − x₀‖ + ‖y − y₀‖`, not the sup norm of `X × Y`. -/
theorem pseudoLipschitz_of_contingent_bound {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : X → Set Y) (hF : IsClosed (graphOf F)) (x₀ : X) (y₀ : Y) (h₀ : y₀ ∈ F x₀)
    (α η c : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hη : 0 < η) (hc : 0 < c)
    (hDF : ∀ (x : X) (y : Y), y ∈ F x → ‖x - x₀‖ + ‖y - y₀‖ ≤ η → ∀ v : Y,
      ∃ (u : X) (w : Y), (∃ z ∈ contingentDeriv F x y u, v = z + w) ∧
        ‖u‖ ≤ c * ‖v‖ ∧ ‖w‖ ≤ α * ‖v‖)
    (r ℓ : ℝ) (hr : r = η * (1 - α) / (3 * (1 + α + c))) (hℓ : ℓ = (c + 2 * α) / (1 - α)) :
    (∀ y ∈ Metric.ball y₀ r, (invMap F y ∩ Metric.closedBall x₀ (ℓ * r)).Nonempty) ∧
    ∀ y₁ ∈ Metric.ball y₀ r, ∀ y₂ ∈ Metric.ball y₀ r,
      ∀ x ∈ invMap F y₁ ∩ Metric.closedBall x₀ (ℓ * r),
        Metric.infEDist x (invMap F y₂ ∩ Metric.closedBall x₀ (3 * ℓ * r)) ≤
          ENNReal.ofReal (ℓ * ‖y₁ - y₂‖) := by sorry

end AubinLipschitz
