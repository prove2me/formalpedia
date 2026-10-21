-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_proposition_3
-- name    : BleedFeed.ControlLimit.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:45.938255+00:00
-- url     : https://prove2.me/theorems/46e68202-d3ba-42bd-b906-546f3cdb2c4d
-- title:
--   Proposition 3, p. 15 — under Condition (5) and Assumption 1, $v(i,\mu^+,n)\le v(i,\mu,n)$ from the critical age of $\mu^+$ on
-- statement:
--   In the bleed–feed model (see the definition file), assume Assumption 1 (bleed–feed is optimal in every state $(I-1,\mu,n)$ with $\mu\in\mathcal M$, $n<N$) and Condition (5):
--   $$
--   \frac{r_{i-1,\mu^+}-r_{i-1,\mu}}{r_{i\mu^+}}\le p_{i-1,\mu}-p_{i-1,\mu^+}\qquad\text{for all }\tilde\imath_{\mu^+}<i<I,\ \mu\le\mu^+\in\mathcal M .
--   $$
--   Then for all $\mu\le\mu^+$ in $\mathcal M$, every $n<N$ and every age $i$ with $\tilde\imath_{\mu^+}\le i\le I$,
--   $$
--   v(i,\mu^+,n)\le v(i,\mu,n).
--   $$
--
--   From the critical age of the faster culture on, a higher growth rate is never worth more: its higher rewards are offset by a higher risk of entering the stationary phase. This is the first step towards the growth-rate threshold of Theorem 2.
--
--   **Formalization Note** Two deviations from the page are disclosed. (a) Condition (5) is stated on $\tilde\imath_{\mu^+}<i<I$; the page prints $\tilde\imath_{\mu^+}\le i<I$, a range on which (5) fails for every $\mu<\mu^+$ whenever $\tilde\imath_{\mu^+}\ge 1$, and the proof (p. 34) uses (5) only on the corrected range. (b) Assumption 1 is a hypothesis: §4.2 declares it "valid throughout this section" and the proof uses it in the first induction step.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 15, Proposition 3 and Condition (5); Assumption 1 (p. 15, standing in §4.2)

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Proposition 3, p. 15: under Condition (5) (on the range ĩ_{µ⁺} < i < I) and Assumption 1, for
µ ≤ µ⁺ in ℳ and n < N, v(i, µ⁺, n) ≤ v(i, µ, n) for all ĩ_{µ⁺} ≤ i ≤ I. -/
theorem proposition_3 (P : Params) (hS : P.Standing) (h5 : Condition5 P) (hA1 : Assumption1 P)
    (μ μ' : ℝ) (hμ : μ ∈ P.rates) (hμ' : μ' ∈ P.rates) (hle : μ ≤ μ') (n : ℕ) (hn : n < P.N)
    (i : ℕ) (hi₁ : critAge P μ' ≤ i) (hi₂ : i ≤ P.I) :
    v P i μ' n ≤ v P i μ n := by sorry

end BleedFeed.ControlLimit
