-- Prove2me | Theorems.Thm_DCAThirty_DStat_theorem_1_ii_a
-- name    : DCAThirty.DStat.theorem_1_ii_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:37.515206+00:00
-- url     : https://prove2.me/theorems/6114602c-7451-428a-9613-9035e1796110
-- title:
--   Theorem 1(ii), p. 9 — for x ∈ dom g with ∂h(x) ≠ ∅, x is d-stationary for f iff g′(x; u) ≥ h′(x; u) for all u ∈ X
-- statement:
--   Let $X=\mathbb R^n$, let $g,h\in\Gamma_0(X)$ (proper, lower semicontinuous, convex, with values in $\mathbb R\cup\{+\infty\}$), and let $f=g-h$ be the DC objective of the program $(P_{dc})$, with the convention $+\infty-(+\infty)=+\infty$. Assume that the optimal value $\alpha=\inf_{x\in X}f(x)$ is finite; this implies $\operatorname{dom} g\subset\operatorname{dom} h$ and $\operatorname{dom} f=\operatorname{dom} g$. For the convex components, $g'(x;u)=\inf_{t>0}\frac{g(x+tu)-g(x)}{t}$ and likewise $h'(x;u)$; $f'(x;u)$ is the limit $\lim_{t\downarrow0}\frac{f(x+tu)-f(x)}{t}$ in $\mathbb R\cup\{\pm\infty\}$.
--
--   Let $x\in\operatorname{dom} g$ with $\partial h(x)\ne\emptyset$. Then $x$ is d-stationary for $f$ (that is, $f'(x;u)$ exists and is $\ge0$ for every $u\in X$) if and only if
--
--   $$g'(x;u)\ge h'(x;u)\qquad\text{for all }u\in X.$$
--
--   This turns d-stationarity of the nonconvex $f$ into a comparison of the directional derivatives of two convex functions, which is the form in which it is related to subdifferentials in the later parts of Theorem 1.
--
--   **Formalization Note** The hypothesis $\partial h(x)\ne\emptyset$ is added; without it the "if" direction is false. Take $n=1$, $g(t)=-2\sqrt t$ on $[0,1]$, $h(t)=-\sqrt t$ on $[0,\infty)$ (both $+\infty$ elsewhere): then $\alpha=-1$, and at $x=0$ one has $g'(0;u)\ge h'(0;u)$ for every $u$, but $f'(0;1)=-\infty$. The page's "the vector $x\in X$" is read as $x\in\operatorname{dom} g$, since a point outside $\operatorname{dom} f=\operatorname{dom} g$ is never d-stationary and $g'(x;\cdot)$ is defined on $\operatorname{dom} g$ only. $\operatorname{ri}$ is Mathlib's `intrinsicInterior ℝ` (interior relative to the affine hull), d-stationarity requires that $f'(x;u)$ exist in every direction, and strong criticality contains the nonemptiness $\partial h(x)\ne\emptyset$.
-- source:
--   Le Thi & Pham Dinh, DC programming and DCA: thirty years of developments, Math. Program. 169 (2018), p. 9, Theorem 1(ii), first sentence

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting
import Definitions.Def_DCAThirty_DStat_Setting

open TaoAnDCA.GlobalOpt ThreeOpSplitting.ConvexRates Filter Topology

namespace DCAThirty.DStat

/-- Theorem 1(ii), first sentence (p. 9), with the added hypothesis `∂h(x) ≠ ∅`: for
`x ∈ dom g`, `x` is d-stationary for `f = g − h` iff `g′(x; u) ≥ h′(x; u)` for all `u`. As printed
the "if" direction is false: `g(t) = −2√t` on `[0, 1]`, `h(t) = −√t` on `[0, ∞)`, `x = 0`. -/
theorem theorem_1_ii_a {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : IsProperClosedConvex g) (hh : IsProperClosedConvex h)
    (hα : primalValue g h ≠ ⊥) (hα' : primalValue g h ≠ ⊤)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ effDom g)
    (hsub : (subdiff h x).Nonempty) :
    IsDStationary (dcSub g h) x ↔ ∀ u, convDirDeriv h x u ≤ convDirDeriv g x u := by sorry

end DCAThirty.DStat
