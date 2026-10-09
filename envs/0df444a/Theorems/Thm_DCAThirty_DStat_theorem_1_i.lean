-- Prove2me | Theorems.Thm_DCAThirty_DStat_theorem_1_i
-- name    : DCAThirty.DStat.theorem_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:11:20.222571+00:00
-- url     : https://prove2.me/theorems/a31afe16-33ef-42b8-8db9-74718f43194e
-- title:
--   Theorem 1(i), p. 9 — for x ∈ dom g with ∂h(x) ≠ ∅, f′(x; u) = g′(x; u) − h′(x; u) for all u ∈ X
-- statement:
--   Let $X=\mathbb R^n$, let $g,h\in\Gamma_0(X)$ (proper, lower semicontinuous, convex, with values in $\mathbb R\cup\{+\infty\}$), and let $f=g-h$ be the DC objective of the program $(P_{dc})$, with the convention $+\infty-(+\infty)=+\infty$. Assume that the optimal value $\alpha=\inf_{x\in X}f(x)$ is finite; this implies $\operatorname{dom} g\subset\operatorname{dom} h$ and $\operatorname{dom} f=\operatorname{dom} g$. For the convex components, $g'(x;u)=\inf_{t>0}\frac{g(x+tu)-g(x)}{t}$ and likewise $h'(x;u)$; $f'(x;u)$ is the limit $\lim_{t\downarrow0}\frac{f(x+tu)-f(x)}{t}$ in $\mathbb R\cup\{\pm\infty\}$.
--
--   Let $x\in\operatorname{dom} g$ with $\partial h(x)\ne\emptyset$. Then for every $u\in X$ the directional derivative $f'(x;u)$ exists in $\mathbb R\cup\{\pm\infty\}$ and
--
--   $$f'(x;u)=g'(x;u)-h'(x;u),$$
--
--   where the right side is $+\infty$ whenever $g'(x;u)=+\infty$.
--
--   This is the calculus rule underlying the whole of Theorem 1: it reduces the directional derivative of the nonconvex function $f$ to those of its convex components, for which convex analysis supplies formulas in terms of subdifferentials.
--
--   **Formalization Note** The hypothesis $\partial h(x)\ne\emptyset$ is added; it is not on the page, and part (i) is false without it. Take $n=1$, $g(t)=-\sqrt t$ on $[0,1]$, $h(t)=-2\sqrt t$ on $[0,\infty)$ (both $+\infty$ elsewhere): then $f=\sqrt t$ on $[0,1]$, $\alpha=0$, and at $x=0$, $u=1$ one has $f'(0;1)=+\infty$ while $g'(0;1)=h'(0;1)=-\infty$. With $\partial h(x)\ne\emptyset$, $h'(x;u)>-\infty$, so the difference is well defined. The page leaves $x$ unquantified; it is taken in $\operatorname{dom} g=\operatorname{dom} f$, where the paper defines $f'(x;\cdot)$. The case $g'(x;u)=+\infty$ is written out explicitly because Lean's extended reals have $\top-\top=\bot$. The existence of the limit is part of the conclusion.
-- source:
--   Le Thi & Pham Dinh, DC programming and DCA: thirty years of developments, Math. Program. 169 (2018), p. 9, Theorem 1(i)

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting
import Definitions.Def_DCAThirty_DStat_Setting

open TaoAnDCA.GlobalOpt ThreeOpSplitting.ConvexRates Filter Topology

namespace DCAThirty.DStat

/-- Theorem 1(i) (p. 9), with the added hypothesis `∂h(x) ≠ ∅`: for `x ∈ dom g`,
`f′(x; u) = g′(x; u) − h′(x; u)` for every `u`, where `+∞ − (+∞) = +∞`. As printed (without
`∂h(x) ≠ ∅`) the part is false: `g(t) = −√t` on `[0, 1]`, `h(t) = −2√t` on `[0, ∞)`, `x = 0`,
`u = 1` give `f′ = +∞`, `g′ = h′ = −∞`. -/
theorem theorem_1_i {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : IsProperClosedConvex g) (hh : IsProperClosedConvex h)
    (hα : primalValue g h ≠ ⊥) (hα' : primalValue g h ≠ ⊤)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ effDom g)
    (hsub : (subdiff h x).Nonempty) :
    ∀ u, HasDirDerivE (dcSub g h) x u
      (if convDirDeriv g x u = ⊤ then ⊤ else convDirDeriv g x u - convDirDeriv h x u) := by sorry

end DCAThirty.DStat
