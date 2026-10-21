-- Prove2me | Theorems.Thm_BuyXFree_Threshold_lemma_5
-- name    : BuyXFree.Threshold.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:26.49029+00:00
-- url     : https://prove2.me/theorems/481b7429-2929-45ff-b3ef-975708b88a55
-- title:
--   Lemma 5, p. 37 — buying in state X−1 against v̄ implies redeeming in state X against v̄
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. For any price $p$,
--   $$v-p+\delta J(X)\ge\bar v+\delta J(X-1)\ \Longrightarrow\ v+k+\delta J(0)\ge\bar v+\delta J(X).$$
--
--   If the consumer buys in state $X-1$ against the high outside option, she also redeems in state $X$ against it.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 37, Lemma 5

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Lemma 5, p. 37: for any price `p`, if `v − p + δJ(X) ≥ v̄ + δJ(X − 1)` then
`v + k + δJ(0) ≥ v̄ + δJ(X)`. -/
theorem lemma_5 (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J)
    (h : P.v - p + P.δ * J X ≥ P.vbar + P.δ * J (X - 1)) :
    P.v + P.k + P.δ * J 0 ≥ P.vbar + P.δ * J X := by sorry
end BuyXFree.Threshold
