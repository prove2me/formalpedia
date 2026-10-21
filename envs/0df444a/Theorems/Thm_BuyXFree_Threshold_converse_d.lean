-- Prove2me | Theorems.Thm_BuyXFree_Threshold_converse_d
-- name    : BuyXFree.Threshold.converse_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:29.691796+00:00
-- url     : https://prove2.me/theorems/28cd9227-8ce4-455b-b0eb-76a474c887bb
-- title:
--   Proof of Lemma 9, p. 42 — (31)–(32) force p^D(X) < p ≤ ((1−A^{X+1})v + A^X(1−A)k)/(1−A^X)
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Assume moreover $\lambda>0$ and $q>0$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. If
--   $$v-p+\delta J(1)\ge\delta J(0)\ (31),\qquad v+k+\delta J(0)<\bar v+\delta J(X)\ (32),$$
--   then
--   $$p^D(X)<p\le\frac{(1-A^{X+1})v+A^X(1-A)k}{1-A^X}.$$
--
--   This is the converse of Proposition 2(d).
--
--   **Formalization Note** $\lambda>0$, $q>0$ are added: both bounds divide by $1-A^X$ or $A(1-A^X)$.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 42, proof of Lemma 9 (inequalities (31)–(32))

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Proof of Lemma 9, p. 42: inequalities (31)–(32) force
`p ≤ ((1 − A^{X+1})v + A^X(1 − A)k)/(1 − A^X)` and `p > p^D(X)`. Added hypothesis: `λ > 0`,
`q > 0`. -/
theorem converse_d (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q)
    (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J)
    (h31 : BuysLow P p J 0) (h32 : ¬ RedeemsHigh P X J) :
    p ≤ pdUpper P X ∧ pD P X X < p := by sorry
end BuyXFree.Threshold
