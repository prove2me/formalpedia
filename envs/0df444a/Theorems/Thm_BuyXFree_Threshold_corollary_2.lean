-- Prove2me | Theorems.Thm_BuyXFree_Threshold_corollary_2
-- name    : BuyXFree.Threshold.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:34.612867+00:00
-- url     : https://prove2.me/theorems/4ab0853f-1ce2-4c03-9d7a-a6296773ea30
-- title:
--   Corollary 2, p. 9 — for p ≥ 0 the willingness to purchase increases with the point inventory, inequality (3)
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. If $p\ge0$, then for $0\le x\le X-2$
--   $$v-p+\delta J(x+2)-\bigl(\bar v+\delta J(x+1)\bigr)\ \ge\ v-p+\delta J(x+1)-\bigl(\bar v+\delta J(x)\bigr).\qquad(3)$$
--
--   The gain of buying over the high outside option grows with the point inventory ("point pressure").
--
--   **Formalization Note** The page says "for any price $p$"; the hypothesis $p\ge0$ is added because (3) is the convexity of Proposition 1 rearranged, and that convexity fails for negative prices (same example as in Proposition 1).
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 9, Corollary 2, inequality (3)

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Corollary 2, inequality (3), p. 9: for a nonnegative price and `0 ≤ x ≤ X − 2`, the gain of
buying over taking the outside option `v̄` is larger in state `x + 1` than in state `x`. -/
theorem corollary_2 (P : Params) (hP : P.Standing) (p : ℝ) (hp : 0 ≤ p) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J) (x : ℕ) (hx : x + 2 ≤ X) :
    P.v - p + P.δ * J (x + 2) - (P.vbar + P.δ * J (x + 1)) ≥
      P.v - p + P.δ * J (x + 1) - (P.vbar + P.δ * J x) := by sorry
end BuyXFree.Threshold
