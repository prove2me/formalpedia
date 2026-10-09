-- Prove2me | Theorems.Thm_DCAThirty_DStat_theorem_1_v
-- name    : DCAThirty.DStat.theorem_1_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:10:07.714982+00:00
-- url     : https://prove2.me/theorems/ae44b306-953f-49a2-afff-93907498294d
-- title:
--   Theorem 1(v), p. 9 — for x ∈ ri(dom h), strong criticality ∅ ≠ ∂h(x) ⊂ ∂g(x) implies d-stationarity of x
-- statement:
--   Let $X=\mathbb R^n$, let $g,h\in\Gamma_0(X)$ (proper, lower semicontinuous, convex, with values in $\mathbb R\cup\{+\infty\}$), and let $f=g-h$ be the DC objective of the program $(P_{dc})$, with the convention $+\infty-(+\infty)=+\infty$. Assume that the optimal value $\alpha=\inf_{x\in X}f(x)$ is finite; this implies $\operatorname{dom} g\subset\operatorname{dom} h$ and $\operatorname{dom} f=\operatorname{dom} g$. For the convex components, $g'(x;u)=\inf_{t>0}\frac{g(x+tu)-g(x)}{t}$ and likewise $h'(x;u)$; $f'(x;u)$ is the limit $\lim_{t\downarrow0}\frac{f(x+tu)-f(x)}{t}$ in $\mathbb R\cup\{\pm\infty\}$.
--
--   Let $x\in\operatorname{ri}(\operatorname{dom} h)$. If $x$ is strongly critical, that is $\emptyset\ne\partial h(x)\subset\partial g(x)$, then $x$ is d-stationary for $f$:
--
--   $$f'(x;u)\ge0\qquad\text{for all }u\in X.$$
--
--   This is the direction "strongly critical $\Rightarrow$ d-stationary" of the equivalence in part (iii). Together with part (iv) it shows that the points DCA computes are directionally stationary for the DC objective whenever they lie in the relative interior of $\operatorname{dom} h$.
--
--   **Formalization Note** The statement is as printed. $\operatorname{ri}$ is Mathlib's `intrinsicInterior ℝ` (interior relative to the affine hull), d-stationarity requires that $f'(x;u)$ exist in every direction, and strong criticality contains the nonemptiness $\partial h(x)\ne\emptyset$.
-- source:
--   Le Thi & Pham Dinh, DC programming and DCA: thirty years of developments, Math. Program. 169 (2018), p. 9, Theorem 1(v)

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting
import Definitions.Def_DCAThirty_DStat_Setting

open TaoAnDCA.GlobalOpt ThreeOpSplitting.ConvexRates Filter Topology

namespace DCAThirty.DStat

/-- Theorem 1(v) (p. 9), as printed: if `x ∈ ri(dom h)`, strong criticality of `x` implies
d-stationarity of `x` for `f = g − h`. -/
theorem theorem_1_v {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : IsProperClosedConvex g) (hh : IsProperClosedConvex h)
    (hα : primalValue g h ≠ ⊥) (hα' : primalValue g h ≠ ⊤)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ intrinsicInterior ℝ (effDom h)) :
    IsStronglyCritical g h x → IsDStationary (dcSub g h) x := by sorry

end DCAThirty.DStat
