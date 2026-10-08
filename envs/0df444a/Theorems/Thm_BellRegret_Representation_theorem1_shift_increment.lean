-- Prove2me | Theorems.Thm_BellRegret_Representation_theorem1_shift_increment
-- name    : BellRegret.Representation.theorem1_shift_increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:13.286985+00:00
-- url     : https://prove2.me/theorems/529d5c30-8bc9-4426-a748-772b45d5e2d3
-- title:
--   Proof of Theorem 1, p. 970 — u(x + h, y + h) − u(x, y) = j(h)
-- statement:
--   Let $u(x,y)$ be strictly increasing in $x$ and strictly decreasing in $y$, take the value function $v(x)=x$, and suppose Assumptions 2 and 3 hold. Then there is a function $j:\mathbb R\to\mathbb R$ such that for all $x,y,h$
--   $$u(x+h,\,y+h)-u(x,y)=j(h).$$
--   This is the key step of the proof of Theorem 1: shifting both final and foregone assets by $h$ changes utility by an amount that depends on $h$ alone. It is where Assumption 3, which compares choices between different pairs of alternatives, separates $u(x,y)$ from $u(y,x)$.
--
--   **Formalization Note** The page writes this step for $v(x)=x$; the hypotheses are Assumptions 2 and 3 with $v=\mathrm{id}$. "Increasing/decreasing" (p. 965) is read strictly. The function $j$ is chosen before $x$, $y$, $h$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 970 (PDF 11), proof of Theorem 1

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

namespace BellRegret.Representation

/-- Bell (1982), proof of Theorem 1, p. 970: for `v(x) = x`, Assumptions 2 and 3 imply
`u(x + h, y + h) - u(x, y) = j(h)` for some function `j` not depending on `x`, `y`. -/
theorem theorem1_shift_increment (u : ℝ → ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hA2 : Assumption2 u id) (hA3 : Assumption3 u id) :
    ∃ j : ℝ → ℝ, ∀ x y h : ℝ, u (x + h) (y + h) - u x y = j h := by sorry

end BellRegret.Representation
