-- Prove2me | Theorems.Thm_BuyXFree_Threshold_converse_a
-- name    : BuyXFree.Threshold.converse_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:25.656595+00:00
-- url     : https://prove2.me/theorems/50bea9f7-2769-41f2-82c1-59f7242c7a25
-- title:
--   Proof of Lemma 6, p. 39 — purchasing in state 0 against v̄, (24), forces p ≤ p^D(0)
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Assume moreover $\lambda>0$ and $q>0$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. If the consumer buys in state $0$ against the high outside option,
--   $$v-p+\delta J(1)\ge\bar v+\delta J(0)\qquad(24),$$
--   then $p\le p^D(0)$.
--
--   This is the converse of Proposition 2(a), established in the proof of Lemma 6: any price at which the consumer buys from state $0$ even against $\bar v$ lies in the range of case (a).
--
--   **Formalization Note** $\lambda>0$, $q>0$ are added for uniformity with Proposition 2; the paper's derivation divides by $\lambda$.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 39, proof of Lemma 6 (inequality (24))

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Proof of Lemma 6, p. 39: if the consumer buys in state `0` facing the high outside option
(inequality (24)), then `p ≤ p^D(0)`. Added hypothesis: `λ > 0`, `q > 0`. -/
theorem converse_a (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q)
    (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J)
    (h24 : BuysHigh P p J 0) :
    p ≤ pD P X 0 := by sorry
end BuyXFree.Threshold
