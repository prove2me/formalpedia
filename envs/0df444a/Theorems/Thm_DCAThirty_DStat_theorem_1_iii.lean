-- Prove2me | Theorems.Thm_DCAThirty_DStat_theorem_1_iii
-- name    : DCAThirty.DStat.theorem_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:55.352008+00:00
-- url     : https://prove2.me/theorems/3779586f-054c-405a-8a49-a5888c5085a3
-- title:
--   Theorem 1(iii), p. 9 — at x ∈ ri(dom g) ∩ ri(dom h), x is d-stationary for f = g − h iff ∅ ≠ ∂h(x) ⊂ ∂g(x)
-- statement:
--   Let $X=\mathbb R^n$, let $g,h\in\Gamma_0(X)$ (proper, lower semicontinuous, convex, with values in $\mathbb R\cup\{+\infty\}$), and let $f=g-h$ be the DC objective of the program $(P_{dc})$, with the convention $+\infty-(+\infty)=+\infty$. Assume that the optimal value $\alpha=\inf_{x\in X}f(x)$ is finite; this implies $\operatorname{dom} g\subset\operatorname{dom} h$ and $\operatorname{dom} f=\operatorname{dom} g$. For the convex components, $g'(x;u)=\inf_{t>0}\frac{g(x+tu)-g(x)}{t}$ and likewise $h'(x;u)$; $f'(x;u)$ is the limit $\lim_{t\downarrow0}\frac{f(x+tu)-f(x)}{t}$ in $\mathbb R\cup\{\pm\infty\}$.
--
--   Let $x\in\operatorname{ri}(\operatorname{dom} g)\cap\operatorname{ri}(\operatorname{dom} h)$. Then $x$ is d-stationary for $f$ if and only if $x$ is a strongly critical point of $f=g-h$:
--
--   $$\bigl(f'(x;u)\ge0\ \ \forall u\in X\bigr)\iff\emptyset\ne\partial h(x)\subset\partial g(x).$$
--
--   This is the paper's justification of DCA as a method for d-stationary points: DCA computes (strongly) critical points, and under this relative-interior condition strong criticality and directional stationarity coincide.
--
--   **Formalization Note** The statement is as printed; no hypothesis is added. $\operatorname{ri}$ is Mathlib's `intrinsicInterior ℝ` (interior relative to the affine hull), d-stationarity requires that $f'(x;u)$ exist in every direction, and strong criticality contains the nonemptiness $\partial h(x)\ne\emptyset$.
-- source:
--   Le Thi & Pham Dinh, DC programming and DCA: thirty years of developments, Math. Program. 169 (2018), p. 9, Theorem 1(iii)

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting
import Definitions.Def_DCAThirty_DStat_Setting

open TaoAnDCA.GlobalOpt ThreeOpSplitting.ConvexRates Filter Topology

namespace DCAThirty.DStat

/-- Theorem 1(iii) (p. 9), as printed: if `x ∈ ri(dom g) ∩ ri(dom h)`, then `x` is
d-stationary for `f = g − h` iff `x` is strongly critical, `∅ ≠ ∂h(x) ⊂ ∂g(x)`. -/
theorem theorem_1_iii {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : IsProperClosedConvex g) (hh : IsProperClosedConvex h)
    (hα : primalValue g h ≠ ⊥) (hα' : primalValue g h ≠ ⊤)
    (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ intrinsicInterior ℝ (effDom g) ∩ intrinsicInterior ℝ (effDom h)) :
    IsDStationary (dcSub g h) x ↔ IsStronglyCritical g h x := by sorry

end DCAThirty.DStat
