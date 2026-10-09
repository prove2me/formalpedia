-- Prove2me | Theorems.Thm_DCAThirty_DStat_theorem_1_iv
-- name    : DCAThirty.DStat.theorem_1_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:45.717197+00:00
-- url     : https://prove2.me/theorems/0065b01c-8f0a-491c-9dca-92596c29e1a5
-- title:
--   Theorem 1(iv), p. 9 — for x ∈ ri(dom g) with ∂h(x) ≠ ∅, d-stationarity of x implies strong criticality ∅ ≠ ∂h(x) ⊂ ∂g(x)
-- statement:
--   Let $X=\mathbb R^n$, let $g,h\in\Gamma_0(X)$ (proper, lower semicontinuous, convex, with values in $\mathbb R\cup\{+\infty\}$), and let $f=g-h$ be the DC objective of the program $(P_{dc})$, with the convention $+\infty-(+\infty)=+\infty$. Assume that the optimal value $\alpha=\inf_{x\in X}f(x)$ is finite; this implies $\operatorname{dom} g\subset\operatorname{dom} h$ and $\operatorname{dom} f=\operatorname{dom} g$. For the convex components, $g'(x;u)=\inf_{t>0}\frac{g(x+tu)-g(x)}{t}$ and likewise $h'(x;u)$; $f'(x;u)$ is the limit $\lim_{t\downarrow0}\frac{f(x+tu)-f(x)}{t}$ in $\mathbb R\cup\{\pm\infty\}$.
--
--   Let $x\in\operatorname{ri}(\operatorname{dom} g)$ with $\partial h(x)\ne\emptyset$. If $x$ is d-stationary for $f$, then $x$ is strongly critical:
--
--   $$\emptyset\ne\partial h(x)\subset\partial g(x).$$
--
--   This is the direction "d-stationary $\Rightarrow$ strongly critical" of the equivalence in part (iii); it shows that strong criticality, which DCA produces, is never stronger than d-stationarity where $\partial h$ is nonempty.
--
--   **Formalization Note** The hypothesis $\partial h(x)\ne\emptyset$ is added; as printed, part (iv) is false. Take $n=2$, $g$ the indicator of $\{0\}\times[0,1]$ and $h(x_1,x_2)=-\sqrt{x_1}$ for $x_1\ge0$ ($+\infty$ otherwise): then $f=0$ on $\operatorname{dom} g$, $\alpha=0$, and $x=(0,\tfrac12)\in\operatorname{ri}(\operatorname{dom} g)$ is d-stationary, but $\partial h(x)=\emptyset$, so $x$ is not strongly critical. The hypothesis $x\in\operatorname{ri}(\operatorname{dom} g)$ is kept as printed. $\operatorname{ri}$ is Mathlib's `intrinsicInterior ℝ` (interior relative to the affine hull), d-stationarity requires that $f'(x;u)$ exist in every direction, and strong criticality contains the nonemptiness $\partial h(x)\ne\emptyset$.
-- source:
--   Le Thi & Pham Dinh, DC programming and DCA: thirty years of developments, Math. Program. 169 (2018), p. 9, Theorem 1(iv)

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting
import Definitions.Def_DCAThirty_DStat_Setting

open TaoAnDCA.GlobalOpt ThreeOpSplitting.ConvexRates Filter Topology

namespace DCAThirty.DStat

/-- Theorem 1(iv) (p. 9), with the added hypothesis `∂h(x) ≠ ∅`: if `x ∈ ri(dom g)`,
d-stationarity of `x` implies strong criticality of `x`. As printed it is false: `n = 2`, `g` the
indicator of `{0} × [0, 1]`, `h(x₁, x₂) = −√x₁` on `x₁ ≥ 0`, `x = (0, 1/2)`. -/
theorem theorem_1_iv {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : IsProperClosedConvex g) (hh : IsProperClosedConvex h)
    (hα : primalValue g h ≠ ⊥) (hα' : primalValue g h ≠ ⊤)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ intrinsicInterior ℝ (effDom g))
    (hsub : (subdiff h x).Nonempty) :
    IsDStationary (dcSub g h) x → IsStronglyCritical g h x := by sorry

end DCAThirty.DStat
