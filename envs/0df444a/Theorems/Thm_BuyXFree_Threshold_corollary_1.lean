-- Prove2me | Theorems.Thm_BuyXFree_Threshold_corollary_1
-- name    : BuyXFree.Threshold.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:21.113074+00:00
-- url     : https://prove2.me/theorems/48db5581-1692-41f8-906c-89b9c06ff090
-- title:
--   Corollary 1(a)–(b), pp. 8–9 — buying in state x implies buying in state x+1, under either outside option
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. For any price $p$ and $0\le x\le X-2$:
--
--   1. if $v-p+\delta J(x+1)\ge\delta J(x)$, then $v-p+\delta J(x+2)\ge\delta J(x+1)$ (outside option $0$);
--   2. if $v-p+\delta J(x+1)\ge\bar v+\delta J(x)$, then $v-p+\delta J(x+2)\ge\bar v+\delta J(x+1)$ (outside option $\bar v$).
--
--   $$\text{buying in state }x\ \Longrightarrow\ \text{buying in state }x+1.$$
--
--   Purchase decisions are therefore of threshold type in the point inventory, under either value of the outside option.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), pp. 8–9, Corollary 1

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Corollary 1, pp. 8–9: for any price `p` and `0 ≤ x ≤ X − 2`, (a) with outside option `0`
and (b) with outside option `v̄`, buying in state `x` implies buying in state `x + 1`. -/
theorem corollary_1 (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J) (x : ℕ) (hx : x + 2 ≤ X) :
    (P.δ * J x ≤ P.v - p + P.δ * J (x + 1) →
        P.δ * J (x + 1) ≤ P.v - p + P.δ * J (x + 2)) ∧
      (P.vbar + P.δ * J x ≤ P.v - p + P.δ * J (x + 1) →
        P.vbar + P.δ * J (x + 1) ≤ P.v - p + P.δ * J (x + 2)) := by sorry
end BuyXFree.Threshold
