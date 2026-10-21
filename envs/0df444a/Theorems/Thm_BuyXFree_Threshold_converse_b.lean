-- Prove2me | Theorems.Thm_BuyXFree_Threshold_converse_b
-- name    : BuyXFree.Threshold.converse_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:24.444067+00:00
-- url     : https://prove2.me/theorems/4cf458e0-621c-45b3-9d94-d64a0b5e69c6
-- title:
--   Proof of Lemma 7, p. 40 — (25)–(27) with threshold τ force p^D(τ−1) < p ≤ min{p^B(τ), p^D(τ)}
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Assume moreover $\lambda>0$ and $q>0$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. Let $1\le\tau\le X-1$. If
--   $$v-p+\delta J(1)\ge\delta J(0)\ (25),\qquad v-p+\delta J(\tau+1)\ge\bar v+\delta J(\tau)\ (26),\qquad v-p+\delta J(\tau)<\bar v+\delta J(\tau-1)\ (27),$$
--   then $p\le p^B(\tau)$, $p\le p^D(\tau)$ and $p>p^D(\tau-1)$.
--
--   This is the converse of Proposition 2(b): a consumer who buys from state $0$ at the low outside option and switches to buying at the high outside option exactly at state $\tau$ faces a price in the case (b) range for $\tau$.
--
--   **Formalization Note** $\lambda>0$, $q>0$ are added: the bounds divide by quantities that vanish at $A=0$.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 40, proof of Lemma 7 (inequalities (25)–(27))

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Proof of Lemma 7, p. 40: inequalities (25)–(27) for a threshold `1 ≤ τ ≤ X − 1` force
`p ≤ p^B(τ)`, `p ≤ p^D(τ)` and `p > p^D(τ − 1)`. Added hypothesis: `λ > 0`, `q > 0`. -/
theorem converse_b (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q)
    (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (hJ : IsValueFn P p X J)
    (τ : ℕ) (hτ1 : 1 ≤ τ) (hτX : τ + 1 ≤ X)
    (h25 : BuysLow P p J 0) (h26 : BuysHigh P p J τ) (h27 : ¬ BuysHigh P p J (τ - 1)) :
    p ≤ pB P X τ ∧ p ≤ pD P X τ ∧ pD P X (τ - 1) < p := by sorry
end BuyXFree.Threshold
