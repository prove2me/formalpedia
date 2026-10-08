-- Prove2me | Theorems.Thm_BellRegret_Representation_lemma2
-- name    : BellRegret.Representation.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:12.351732+00:00
-- url     : https://prove2.me/theorems/37c314b3-fae2-4293-b052-1450a4f1a46f
-- title:
--   Lemma 2, p. 968 — Assumptions 1 and 2 imply u(x, y) − u(y, x) = g(v(x) − v(y))
-- statement:
--   Let $u(x,y)$ be a utility over final assets $x$ and foregone assets $y$, strictly increasing in $x$ and strictly decreasing in $y$, and let $v$ be a strictly increasing value function from $\mathbb R$ onto $\mathbb R$. If Assumptions 1 and 2 hold, then there is a function $g:\mathbb R\to\mathbb R$ such that for all $x,y$
--   $$u(x,y)-u(y,x)=g\big(v(x)-v(y)\big).$$
--   Consequently a 50-50 lottery between $x_1$ and $x_2$ is preferred to one between $y_1$ and $y_2$ exactly when $\tfrac12g(v(x_1)-v(y_1))+\tfrac12g(v(x_2)-v(y_2))>0$: in simple comparisons only the regret differences $v(x)-v(y)$ matter.
--
--   **Formalization Note** "Increasing/decreasing" (p. 965) and "strictly monotonic increasing" (p. 968) are read strictly. That $v$ maps onto $\mathbb R$ is an added reading, as in Lemma 1. The function $g$ is chosen before $x$ and $y$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 968 (PDF 9), Lemma 2, first display; proof on p. 969 (PDF 10)

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

namespace BellRegret.Representation

/-- Bell (1982), Lemma 2, p. 968: Assumptions 1 and 2 imply
`u(x, y) - u(y, x) = g(v(x) - v(y))` for some function `g`. -/
theorem lemma2 (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hv : StrictMono v) (hvs : Function.Surjective v)
    (hA1 : Assumption1 u v) (hA2 : Assumption2 u v) :
    ∃ g : ℝ → ℝ, ∀ x y : ℝ, u x y - u y x = g (v x - v y) := by sorry

end BellRegret.Representation
