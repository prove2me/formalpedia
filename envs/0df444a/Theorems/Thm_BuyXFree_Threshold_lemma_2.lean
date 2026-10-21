-- Prove2me | Theorems.Thm_BuyXFree_Threshold_lemma_2
-- name    : BuyXFree.Threshold.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:28.349902+00:00
-- url     : https://prove2.me/theorems/be5b15b4-f6f9-4ac4-b8b3-67741cc5c924
-- title:
--   Lemma 2, p. 13 — with k = 0, π*_b ≤ max{λqv, λ(v − v̄)} if q ≤ 1/2, or q > 1/2 and v − v̄ ≤ v/(1+A1)
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Suppose $k=0$ and either (a) $q\le1/2$, or (b) $q>1/2$ and $v-\bar v\le\frac{v}{1+A_1}$. Then for every threshold $X$, every $\tau\in\{1,\dots,X-1\}$ and every price with $p^D(\tau-1)<p\le\min\{p^B(\tau),p^D(\tau)\}$,
--   $$\frac{\lambda qX}{\tau+q(X-\tau+1)}\,p\ \le\ \max\{\lambda qv,\ \lambda(v-\bar v)\}.$$
--
--   Thus $\pi^*_b$, the optimal value of problem (4), is at most the no-program profit.
--
--   **Formalization Note** $\pi^*_b$ is the supremum of (4) over a possibly empty feasible set; the statement is the equivalent pointwise bound at every feasible $(p,X,\tau)$.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 13, Lemma 2; problem (4), pp. 12–13

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Lemma 2, p. 13, pointwise: with `k = 0`, every feasible point `(p, X, τ)` of problem (4)
(`1 ≤ τ ≤ X − 1`, `p^D(τ − 1) < p ≤ min{p^B(τ), p^D(τ)}`) has objective
`λqX/(τ + q(X − τ + 1)) · p ≤ max{λqv, λ(v − v̄)}` if (a) `q ≤ 1/2` or (b) `q > 1/2` and
`v − v̄ ≤ v/(1 + A₁)`. -/
theorem lemma_2 (P : Params) (hP : P.Standing) (hk : P.k = 0)
    (hcond : P.q ≤ 1 / 2 ∨ (1 / 2 < P.q ∧ P.v - P.vbar ≤ P.v / (1 + A1 P)))
    (X τ : ℕ) (hτ1 : 1 ≤ τ) (hτX : τ + 1 ≤ X) (p : ℝ)
    (hlo : pD P X (τ - 1) < p) (hhi : p ≤ min (pB P X τ) (pD P X τ)) :
    P.lam * P.q * X / ((τ : ℝ) + P.q * ((X : ℝ) - τ + 1)) * p ≤ noProgramProfit P := by sorry
end BuyXFree.Threshold
