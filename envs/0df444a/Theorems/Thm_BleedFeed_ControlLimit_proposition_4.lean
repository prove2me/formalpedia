-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_proposition_4
-- name    : BleedFeed.ControlLimit.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:40.623761+00:00
-- url     : https://prove2.me/theorems/b82fa2c3-d68c-4049-a5fb-0805a7eca554
-- title:
--   Proposition 4, p. 15 — under Condition (5) and Assumption 1, $C(i,\mu,n)-B(n)$ is nonincreasing in $\mu$
-- statement:
--   In the bleed–feed model (see the definition file), assume Condition (5) (on the range $\tilde\imath_{\mu^+}<i<I$) and Assumption 1. Then for all $\mu\le\mu^+$ in $\mathcal M$, every $n<N$ and every age $i$ with $\tilde\imath_{\mu^+}\le i<I-1$,
--   $$
--   C(i,\mu^+,n)-B(n)\le C(i,\mu,n)-B(n).
--   $$
--
--   The advantage of continuing over bleed–feeding shrinks as the growth rate increases: if bleed–feed is optimal for a culture, it is also optimal for a faster one of the same age and count. This yields the growth-rate threshold of Theorem 2.
--
--   **Formalization Note** As in Proposition 3, Condition (5) is stated on the corrected range $\tilde\imath_{\mu^+}<i<I$ (the page prints $\tilde\imath_{\mu^+}\le i<I$, which is unsatisfiable for $\mu<\mu^+$ when $\tilde\imath_{\mu^+}\ge1$), and Assumption 1, the standing assumption of §4.2, is a hypothesis.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 15, Proposition 4

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Proposition 4, p. 15: under Condition (5) (on the range ĩ_{µ⁺} < i < I) and Assumption 1,
C(i, µ⁺, n) − B(n) ≤ C(i, µ, n) − B(n) for ĩ_{µ⁺} ≤ i < I − 1, µ ≤ µ⁺ in ℳ, n < N. -/
theorem proposition_4 (P : Params) (hS : P.Standing) (h5 : Condition5 P) (hA1 : Assumption1 P)
    (μ μ' : ℝ) (hμ : μ ∈ P.rates) (hμ' : μ' ∈ P.rates) (hle : μ ≤ μ') (n : ℕ) (hn : n < P.N)
    (i : ℕ) (hi₁ : critAge P μ' ≤ i) (hi₂ : i < P.I - 1) :
    C P i μ' n - B P n ≤ C P i μ n - B P n := by sorry

end BleedFeed.ControlLimit
