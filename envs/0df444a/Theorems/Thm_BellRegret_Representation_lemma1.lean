-- Prove2me | Theorems.Thm_BellRegret_Representation_lemma1
-- name    : BellRegret.Representation.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:20:48.022118+00:00
-- url     : https://prove2.me/theorems/fe149408-1f81-4e95-ab7a-acbb9131ffa6
-- title:
--   Lemma 1, p. 967 — Assumption 1 implies u(x, y) − u(y, x) = g(v(x) − v(y))exp(−cv(x))
-- statement:
--   Let $u(x,y)$ be a utility over final assets $x$ and foregone assets $y$, strictly increasing in $x$ and strictly decreasing in $y$, and let $v$ be a strictly increasing value function from $\mathbb R$ onto $\mathbb R$. If Assumption 1 holds, then there are a constant $c$ and a function $g:\mathbb R\to\mathbb R$ such that for all $x,y$
--   $$u(x,y)-u(y,x)=g\big(v(x)-v(y)\big)\,e^{-c\,v(x)}.$$
--   Lemma 1 is the first structural consequence of the invariance of preferences under equal incremental-value shifts: the identifiable part of $u$ depends on the regret term $v(x)-v(y)$ and, through an exponential factor, on the value level $v(x)$. Assumption 2 later forces $c=0$ (Lemma 2).
--
--   **Formalization Note** "Increasing/decreasing" (p. 965) and "strictly monotonic increasing" (p. 968) are read strictly. That $v$ maps onto $\mathbb R$ is an added reading: Assumption 1 shifts outcomes by arbitrary equal incremental values, which presupposes that every shifted value is attained. The constant $c$ and the function $g$ are chosen before $x$ and $y$, and $g$ takes only the difference $v(x)-v(y)$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 967 (PDF 8), Lemma 1, first display

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

namespace BellRegret.Representation

/-- Bell (1982), Lemma 1, p. 967: Assumption 1 implies
`u(x, y) - u(y, x) = g(v(x) - v(y)) exp(-c v(x))` for some constant `c` and function `g`. -/
theorem lemma1 (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hv : StrictMono v) (hvs : Function.Surjective v)
    (hA1 : Assumption1 u v) :
    ∃ c : ℝ, ∃ g : ℝ → ℝ, ∀ x y : ℝ,
      u x y - u y x = g (v x - v y) * Real.exp (-(c * v x)) := by sorry

end BellRegret.Representation
