-- Prove2me | Theorems.Thm_BellRegret_Representation_theorem1_linear
-- name    : BellRegret.Representation.theorem1_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:14.001274+00:00
-- url     : https://prove2.me/theorems/4a44c874-3401-4cf4-9f9b-42bfd8050745
-- title:
--   Proof of Theorem 1, v(x) = x, p. 970 (corrected) — u(x, y) = αx + f(x − y), f(x − y) = u(0, y − x)
-- statement:
--   Let $u(x,y)$ be strictly increasing in $x$ and strictly decreasing in $y$, take the value function $v(x)=x$, and suppose Assumptions 2 and 3 hold. Then there is a constant $\alpha$ such that for all $x,y$
--   $$u(x,y)=\alpha x+f(x-y),\qquad f(x-y)=u(0,\,y-x).$$
--   This is Theorem 1 in the case of linear value, the case the paper proves first: utility splits additively into a term in final assets and a term in the regret $x-y$.
--
--   **Formalization Note** The page concludes $u(x,y)=x+f(x-y)$, i.e. $\alpha=1$. That is false as printed: $u(x,y)=x-y$ satisfies every hypothesis but needs $\alpha=0$, and $u(x,y)=x-2y$ needs $\alpha=-1$. The proof shows $u(x+h,y+h)-u(x,y)=j(h)$ with $j$ additive, hence $j(h)=\alpha h$, and then silently takes $\alpha=1$. The statement here keeps $\alpha$ free and does not restrict its sign. "Increasing/decreasing" (p. 965) is read strictly. The constant $\alpha$ is chosen before $x$ and $y$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 970 (PDF 11), proof of Theorem 1, case v(x) = x (coefficient of x corrected)

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

namespace BellRegret.Representation

/-- Bell (1982), proof of Theorem 1, case `v(x) = x`, p. 970, corrected: Assumptions 2 and 3
imply `u(x, y) = αx + f(x - y)` with `f(x - y) = u(0, y - x)`, for some constant `α`.
(The page prints the coefficient `α = 1`; see the Formalization Note.) -/
theorem theorem1_linear (u : ℝ → ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hA2 : Assumption2 u id) (hA3 : Assumption3 u id) :
    ∃ α : ℝ, ∀ x y : ℝ, u x y = α * x + u 0 (y - x) := by sorry

end BellRegret.Representation
