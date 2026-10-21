-- Prove2me | Theorems.Thm_BuyXFree_Threshold_proposition_3
-- name    : BuyXFree.Threshold.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:30.862558+00:00
-- url     : https://prove2.me/theorems/d3a4ca5e-871c-4385-b4c4-8c5b17b0015d
-- title:
--   Proposition 3, p. 13 — with k = 0, under (a) or (b), no BXGO program (p, X) earns long-run revenue above max{λqv, λ(v − v̄)}
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Suppose there is no transaction utility, $k=0$, and either
--
--   1. **(a)** $q\le\frac12$ and $\delta\ge\frac{2}{2+\lambda}$, or
--   2. **(b)** $q>\frac12$ and $v-\bar v\le\min\{Av,\ \frac{v}{1+A_1}\}$.
--
--   Then offering a BXGO program cannot improve the firm's profit: for every price $p\in\mathbb R$, every threshold $X\ge1$ and every solution $J$ of the optimality equations (1)–(2), the average expected revenue $\bar R_N$ over the first $N$ periods of a consumer who starts with $0$ points and follows the decisions of $J$ satisfies
--   $$\limsup_{N\to\infty}\bar R_N\ \le\ \max\{\lambda qv,\ \lambda(v-\bar v)\}.$$
--
--   This is the paper's main result for reward programs without transaction utility: a redemption threshold alone induces purchase acceleration but cannot raise long-run profit above the best price without a program.
--
--   **Formalization Note** The firm's profit is the long-run (Cesàro) average expected revenue per period computed from the transition matrix that the consumer's own decisions induce, not the closed forms of Lemmas 1–3; the bound is stated as "for every $\varepsilon>0$, eventually $\bar R_N\le\max\{\cdot\}+\varepsilon$". Every price is covered, including the gaps between the ranges of Proposition 2 and negative prices.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 13, Proposition 3 (proof p. 47)

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Proposition 3, p. 13: without transaction utility (`k = 0`), if (a) `q ≤ 1/2` and
`δ ≥ 2/(2 + λ)`, or (b) `q > 1/2` and `v − v̄ ≤ min{Av, v/(1 + A₁)}`, then no BXGO program `(p, X)`
improves the firm's profit: for every price `p`, threshold `X ≥ 1` and solution `J` of (1)–(2), the
long-run average expected revenue per period of a consumer who starts with `0` points and follows
the decisions of `J` is at most `max{λqv, λ(v − v̄)}`. -/
theorem proposition_3 (P : Params) (hP : P.Standing) (hk : P.k = 0)
    (hcond : (P.q ≤ 1 / 2 ∧ 2 / (2 + P.lam) ≤ P.δ) ∨
      (1 / 2 < P.q ∧ P.v - P.vbar ≤ min (A P * P.v) (P.v / (1 + A1 P))))
    (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J) :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, avgRevenue P p X J N ≤ noProgramProfit P + ε := by sorry
end BuyXFree.Threshold
