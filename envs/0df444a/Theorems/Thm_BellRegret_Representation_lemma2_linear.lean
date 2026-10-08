-- Prove2me | Theorems.Thm_BellRegret_Representation_lemma2_linear
-- name    : BellRegret.Representation.lemma2_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:20:54.076106+00:00
-- url     : https://prove2.me/theorems/3eab6dcc-cbd6-4085-86ad-6c66ce677f3d
-- title:
--   Lemma 2, linear v, p. 968 — u(x, y) − u(y, x) = u(0, y − x) − u(y − x, 0)
-- statement:
--   Let $u(x,y)$ be a utility over final assets $x$ and foregone assets $y$, strictly increasing in $x$ and strictly decreasing in $y$, and let the value function be linear, $v(x)=ax+b$ with $a>0$. If Assumptions 1 and 2 hold, then for all $x,y$
--   $$u(x,y)-u(y,x)=u(0,\,y-x)-u(y-x,\,0).$$
--   In words: with linear value, the identifiable part of $u$ depends on $x$ and $y$ only through the difference $x-y$. Assumption 2 removes the exponential factor of Lemma 1.
--
--   **Formalization Note** "$v(x)$ linear" is read as increasing affine, $v(x)=ax+b$, $a>0$. "Increasing/decreasing" (p. 965) is read strictly.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 968 (PDF 9), Lemma 2, second display

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

namespace BellRegret.Representation

/-- Bell (1982), Lemma 2, linear case, p. 968: if `v` is linear (increasing affine) in `x`,
Assumptions 1 and 2 imply `u(x, y) - u(y, x) = u(0, y - x) - u(y - x, 0)`. -/
theorem lemma2_linear (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hlin : ∃ a b : ℝ, 0 < a ∧ ∀ x, v x = a * x + b)
    (hA1 : Assumption1 u v) (hA2 : Assumption2 u v) :
    ∀ x y : ℝ, u x y - u y x = u 0 (y - x) - u (y - x) 0 := by sorry

end BellRegret.Representation
