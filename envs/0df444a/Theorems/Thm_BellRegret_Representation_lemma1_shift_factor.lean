-- Prove2me | Theorems.Thm_BellRegret_Representation_lemma1_shift_factor
-- name    : BellRegret.Representation.lemma1_shift_factor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:20:42.753143+00:00
-- url     : https://prove2.me/theorems/a9e74c17-e3bd-47a2-ab30-2e86e47e21c5
-- title:
--   Proof of Lemma 1, p. 967 — w(x + h, y + h) = k(h)w(x, y) with k(h) > 0
-- statement:
--   Let $u(x,y)$ be strictly increasing in $x$ and strictly decreasing in $y$, take the value function $v(x)=x$, and suppose Assumption 1 holds: shifting every outcome of two alternatives by the same amount $h$ never changes which one is preferred. Write
--   $$w(x,y)=u(x,y)-u(y,x)$$
--   for the part of $u$ that simple comparisons can identify. Then there is a function $k:\mathbb R\to(0,\infty)$ such that for all $x,y,h$
--   $$w(x+h,\,y+h)=k(h)\,w(x,y).$$
--   This is the first step of the proof of Lemma 1: shifting all outcomes rescales the difference function by a positive factor that depends only on the shift. It leads to the multiplicative equation $k(x+h)=k(x)k(h)$ and to the exponential factor of Lemma 1.
--
--   **Formalization Note** The page writes this step for $v(x)=x$; the hypothesis is Assumption 1 with $v=\mathrm{id}$. "Increasing/decreasing" (p. 965) is read strictly. The function $k$ is chosen before $x$, $y$, $h$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 967 (PDF 8), proof of Lemma 1

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

namespace BellRegret.Representation

/-- Bell (1982), proof of Lemma 1, p. 967: for `v(x) = x`, Assumption 1 implies
`w(x + h, y + h) = k(h) w(x, y)` with `k(h) > 0`, where `w(x, y) = u(x, y) - u(y, x)`.
The function `k` does not depend on `x`, `y`. -/
theorem lemma1_shift_factor (u : ℝ → ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hA1 : Assumption1 u id) :
    ∃ k : ℝ → ℝ, (∀ h, 0 < k h) ∧
      ∀ x y h : ℝ, u (x + h) (y + h) - u (y + h) (x + h) = k h * (u x y - u y x) := by sorry

end BellRegret.Representation
