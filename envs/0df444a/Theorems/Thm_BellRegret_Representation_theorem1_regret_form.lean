-- Prove2me | Theorems.Thm_BellRegret_Representation_theorem1_regret_form
-- name    : BellRegret.Representation.theorem1_regret_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:33.92022+00:00
-- url     : https://prove2.me/theorems/6dbdad73-89b1-45b3-b9ae-14802b313d91
-- title:
--   Theorem 1, p. 969 (corrected) — Assumptions 2 and 3 imply u(x, y) = αv(x) + f(v(x) − v(y))
-- statement:
--   Let $u(x,y)$ be a utility over final assets $x$ and foregone assets $y$, strictly increasing in $x$ and strictly decreasing in $y$, and let $v$ be a strictly increasing value function from $\mathbb R$ onto $\mathbb R$. If Assumptions 2 and 3 hold, then there are a constant $\alpha$ and a function $f:\mathbb R\to\mathbb R$ such that for all $x,y$
--   $$u(x,y)=\alpha\,v(x)+f\big(v(x)-v(y)\big).$$
--   This is Bell's representation theorem for regret: utility is the sum of a term in the value of final assets and a function of the regret (or rejoicing) $v(x)-v(y)$ felt against the foregone assets. Section 2 of the paper applies this additive form to explain the coexistence of insurance and gambling, the Allais paradox and related behaviour.
--
--   **Formalization Note** The paper prints (4), $u(x,y)=v(x)+f(v(x)-v(y))$, i.e. $\alpha=1$. That is false as printed: $v(x)=x$, $u(x,y)=x-y$ satisfies every hypothesis, yet $x-y=x+f(x-y)$ would force $f(0)=0$ at $x=y=0$ and $f(0)=-1$ at $x=y=1$. The statement keeps the coefficient $\alpha$ free and imposes no sign or normalisation on it. "Increasing/decreasing" (p. 965) and "strictly monotonic increasing" (p. 968) are read strictly; that $v$ maps onto $\mathbb R$ is an added reading, needed for Assumption 3's shifts by arbitrary incremental values. $\alpha$ and $f$ are chosen before $x$ and $y$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 969 (PDF 10), Theorem 1, display (4) (coefficient of v(x) corrected); proof p. 970 (PDF 11)

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

namespace BellRegret.Representation

/-- Bell (1982), Theorem 1, p. 969, corrected: Assumptions 2 and 3 imply
`u(x, y) = α v(x) + f(v(x) - v(y))` for some constant `α` and function `f`.
(The page prints `α = 1`, which fails for `v = id`, `u(x, y) = x - y`.) -/
theorem theorem1_regret_form (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hv : StrictMono v) (hvs : Function.Surjective v)
    (hA2 : Assumption2 u v) (hA3 : Assumption3 u v) :
    ∃ α : ℝ, ∃ f : ℝ → ℝ, ∀ x y : ℝ, u x y = α * v x + f (v x - v y) := by sorry

end BellRegret.Representation
