-- Prove2me | Theorems.Thm_BuyXFree_Threshold_proposition_1
-- name    : BuyXFree.Threshold.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:15.307961+00:00
-- url     : https://prove2.me/theorems/c7f0690c-25c9-4ab5-b8e7-1d05386a9eb2
-- title:
--   Proposition 1, p. 8 — for p ≥ 0 the value function J is increasing and convex on {0, …, X}
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. If the price is nonnegative, $p\ge0$, then $J$ is increasing and convex on $\{0,\dots,X\}$:
--   $$J(x)\le J(x+1)\ \ (0\le x\le X-1),\qquad J(x+1)-J(x)\le J(x+2)-J(x+1)\ \ (0\le x\le X-2).$$
--
--   Each additional point is worth more the closer the consumer is to the threshold; this drives the threshold structure of her purchases.
--
--   **Formalization Note** "Increasing" is weak ($\le$), as in the proof's Case 4. The hypothesis $p\ge0$ is added: for negative prices the statement is false (for instance $p=-1$, $\lambda=0.63$, $q=0.74$, $\delta=0.8$, $v=1$, $\bar v=0.94$, $X=8$ gives a strictly decreasing $J$); the paper treats only nonnegative prices implicitly.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 8, Proposition 1

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Proposition 1, p. 8: for a nonnegative price the value function is increasing on
`{0, …, X}` and convex: `J(x+1) − J(x) ≤ J(x+2) − J(x+1)` for `0 ≤ x ≤ X − 2`. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (p : ℝ) (hp : 0 ≤ p) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J) :
    (∀ x < X, J x ≤ J (x + 1)) ∧
      ∀ x : ℕ, x + 2 ≤ X → J (x + 1) - J x ≤ J (x + 2) - J (x + 1) := by sorry
end BuyXFree.Threshold
