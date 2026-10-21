-- Prove2me | Theorems.Thm_BuyXFree_Threshold_converse_c
-- name    : BuyXFree.Threshold.converse_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:26.941694+00:00
-- url     : https://prove2.me/theorems/7886d7c7-51a7-4f2e-94c3-281cb6e5ac86
-- title:
--   Proof of Lemma 8, p. 41 — (28)–(30) force p^D(X−1) < p ≤ min{p^B(X), p^D(X)}
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Assume moreover $\lambda>0$ and $q>0$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. If
--   $$v-p+\delta J(1)\ge\delta J(0)\ (28),\qquad v-p+\delta J(X)<\bar v+\delta J(X-1)\ (29),\qquad v+k+\delta J(0)\ge\bar v+\delta J(X)\ (30),$$
--   then $p\le p^B(X)$, $p>p^D(X-1)$ and $p\le p^D(X)$.
--
--   This is the converse of Proposition 2(c).
--
--   **Formalization Note** $\lambda>0$, $q>0$ are added: $p^B(X)$ and $p^D(X)$ divide by $q(1-A^X)$ and $A_1q(1-A^X)$, which vanish when $A=0$.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 41, proof of Lemma 8 (inequalities (28)–(30))

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Proof of Lemma 8, p. 41: inequalities (28)–(30) force `p ≤ p^B(X)`, `p > p^D(X − 1)` and
`p ≤ p^D(X)`. Added hypothesis: `λ > 0`, `q > 0`. -/
theorem converse_c (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q)
    (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J)
    (h28 : BuysLow P p J 0) (h29 : ¬ BuysHigh P p J (X - 1)) (h30 : RedeemsHigh P X J) :
    p ≤ pB P X X ∧ pD P X (X - 1) < p ∧ p ≤ pD P X X := by sorry
end BuyXFree.Threshold
