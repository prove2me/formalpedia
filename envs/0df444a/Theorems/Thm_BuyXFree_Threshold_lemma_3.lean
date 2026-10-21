-- Prove2me | Theorems.Thm_BuyXFree_Threshold_lemma_3
-- name    : BuyXFree.Threshold.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:24.932788+00:00
-- url     : https://prove2.me/theorems/645f80d2-4323-4119-a059-df906162e1a0
-- title:
--   Lemma 3, p. 13 — with k = 0, π*_c ≤ max{λqv, λ(v − v̄)} if q ≤ A, or q > A and v − v̄ ≤ Av
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Suppose $k=0$ and either (a) $q\le A$, or (b) $q>A$ and $v-\bar v\le Av$. Then for every threshold $X\ge1$ and every price with $p^D(X-1)<p\le\min\{p^B(X),p^D(X)\}$,
--   $$\frac{\lambda qX}{X+q}\,p\ \le\ \max\{\lambda qv,\ \lambda(v-\bar v)\}.$$
--
--   Thus $\pi^*_c$, the optimal case (c) profit (p. 46), is at most the no-program profit.
--
--   **Formalization Note** Stated pointwise at every feasible $(p,X)$, as for Lemma 2.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 13, Lemma 3; the case (c) problem, p. 46

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Lemma 3, p. 13, pointwise: with `k = 0`, every feasible point `(p, X)` of the case (c) problem
(p. 46: `p^D(X − 1) < p ≤ min{p^B(X), p^D(X)}`) has objective `λqX/(X + q) · p ≤ max{λqv, λ(v − v̄)}`
if (a) `q ≤ A` or (b) `q > A` and `v − v̄ ≤ Av`. -/
theorem lemma_3 (P : Params) (hP : P.Standing) (hk : P.k = 0)
    (hcond : P.q ≤ A P ∨ (A P < P.q ∧ P.v - P.vbar ≤ A P * P.v))
    (X : ℕ) (hX : 1 ≤ X) (p : ℝ)
    (hlo : pD P X (X - 1) < p) (hhi : p ≤ min (pB P X X) (pD P X X)) :
    P.lam * P.q * X / ((X : ℝ) + P.q) * p ≤ noProgramProfit P := by sorry
end BuyXFree.Threshold
