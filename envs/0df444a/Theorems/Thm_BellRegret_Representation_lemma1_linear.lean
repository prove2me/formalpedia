-- Prove2me | Theorems.Thm_BellRegret_Representation_lemma1_linear
-- name    : BellRegret.Representation.lemma1_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:20:51.902297+00:00
-- url     : https://prove2.me/theorems/a1ec9a23-724e-4459-a616-6fdfec32bb0a
-- title:
--   Lemma 1, linear v, p. 967 — u(x, y) − u(y, x) = [u(0, y − x) − u(y − x, 0)]exp(−cx)
-- statement:
--   Let $u(x,y)$ be a utility over final assets $x$ and foregone assets $y$, strictly increasing in $x$ and strictly decreasing in $y$, and let the value function be linear, $v(x)=ax+b$ with $a>0$. If Assumption 1 holds, then there is a constant $c$ such that for all $x,y$
--   $$u(x,y)-u(y,x)=\big[u(0,\,y-x)-u(y-x,\,0)\big]\,e^{-cx}.$$
--   This is the special case of Lemma 1 stated on the page: with linear value, the difference $u(x,y)-u(y,x)$, which is all that simple comparisons reveal, is determined by its values at final assets $0$ up to an exponential factor in $x$.
--
--   **Formalization Note** "$v(x)$ linear in $x$" is read as increasing affine, $v(x)=ax+b$, $a>0$; this contains the proof's case $v(x)=x$. "Increasing/decreasing" (p. 965) is read strictly. The constant $c$ is chosen before $x$ and $y$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 967 (PDF 8), Lemma 1, second display

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

namespace BellRegret.Representation

/-- Bell (1982), Lemma 1, linear case, p. 967: if `v` is linear (increasing affine) in `x`,
Assumption 1 implies `u(x, y) - u(y, x) = [u(0, y - x) - u(y - x, 0)] exp(-cx)` for some
constant `c`. -/
theorem lemma1_linear (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hlin : ∃ a b : ℝ, 0 < a ∧ ∀ x, v x = a * x + b)
    (hA1 : Assumption1 u v) :
    ∃ c : ℝ, ∀ x y : ℝ,
      u x y - u y x = (u 0 (y - x) - u (y - x) 0) * Real.exp (-(c * x)) := by sorry

end BellRegret.Representation
