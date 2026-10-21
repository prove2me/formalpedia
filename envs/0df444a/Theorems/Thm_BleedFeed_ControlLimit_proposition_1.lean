-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_proposition_1
-- name    : BleedFeed.ControlLimit.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:30.890359+00:00
-- url     : https://prove2.me/theorems/7036643b-07b5-4fdf-8cc6-390525bfe38c
-- title:
--   Proposition 1, p. 14 — under Condition (4), $v(i,\mu,n)$ is nonincreasing in the cultivation age $i$
-- statement:
--   In the bleed–feed model (see the definition file), assume Condition (4):
--   $$
--   \frac{r_{i\mu}-r_{i-1,\mu}}{r_{i\mu}}\le p_{i-1,\mu}-p_{i\mu}\qquad\text{for all }\tilde\imath_\mu\le i<I,\ \mu\in\mathcal M .
--   $$
--   Then for every $\mu\in\mathcal M$, $n\in\{0,\dots,N\}$ and $i<I$,
--   $$
--   v(i+1,\mu,n)\le v(i,\mu,n),
--   $$
--   that is, the value function is nonincreasing in the cultivation age on $\{0,\dots,I\}$.
--
--   Condition (4) says the relative growth of the reward is outweighed by the drop in the survival probability; under it an older culture is never worth more than a younger one with the same growth rate and bleed–feed count. This is the first step towards the age threshold of Theorem 1.
--
--   **Formalization Note** In Condition (4), $i-1$ is natural-number subtraction; at $i=0$ the clause reads $0\le 0$.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 14, Proposition 1 and Condition (4)

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Proposition 1, p. 14: under Condition (4), v(i, µ, n) is nonincreasing in i ∈ {0, …, I}
for fixed µ ∈ ℳ and n ∈ {0, …, N}. -/
theorem proposition_1 (P : Params) (hS : P.Standing) (h4 : Condition4 P) (μ : ℝ) (hμ : μ ∈ P.rates)
    (n : ℕ) (hn : n ≤ P.N) (i : ℕ) (hi : i < P.I) :
    v P (i + 1) μ n ≤ v P i μ n := by sorry

end BleedFeed.ControlLimit
