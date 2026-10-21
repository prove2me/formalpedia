-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_proposition_2
-- name    : BleedFeed.ControlLimit.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:25.749025+00:00
-- url     : https://prove2.me/theorems/828b3eb9-4b0e-4404-9777-63be42e66198
-- title:
--   Proposition 2, p. 14 — under Condition (4), $C(i,\mu,n)-B(n)$ is nonincreasing in $i$ from the critical age on
-- statement:
--   In the bleed–feed model (see the definition file), assume Condition (4). Then for every $\mu\in\mathcal M$, every $n\in\{0,\dots,N\}$ and every age $i$ with $\tilde\imath_\mu\le i<I$,
--   $$
--   C(i,\mu,n)-B(n)\le C(i-1,\mu,n)-B(n).
--   $$
--
--   Here $C(i,\mu,n)=r_{i\mu}+p_{i\mu}v(i+1,\mu,n)$ is the value of continuing and $B(n)=\mathbb E[C(0,M,n+1)]$ the value of a bleed–feed. The advantage of continuing over bleed–feeding shrinks as the culture ages, which is what yields the age threshold of Theorem 1.
--
--   **Formalization Note** $i-1$ is natural-number subtraction: when $\tilde\imath_\mu=0$, the case $i=0$ (where the page's index $-1$ is undefined) reads $C(0,\mu,n)-B(n)\le C(0,\mu,n)-B(n)$ and is trivially true.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 14, Proposition 2

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Proposition 2, p. 14: under Condition (4), C(i, µ, n) − B(n) ≤ C(i − 1, µ, n) − B(n) for all
ĩ_µ ≤ i < I, µ ∈ ℳ, n ∈ {0, …, N}. (At i = 0 the ℕ subtraction makes both sides equal.) -/
theorem proposition_2 (P : Params) (hS : P.Standing) (h4 : Condition4 P) (μ : ℝ) (hμ : μ ∈ P.rates)
    (n : ℕ) (hn : n ≤ P.N) (i : ℕ) (hi₁ : critAge P μ ≤ i) (hi₂ : i < P.I) :
    C P i μ n - B P n ≤ C P (i - 1) μ n - B P n := by sorry

end BleedFeed.ControlLimit
