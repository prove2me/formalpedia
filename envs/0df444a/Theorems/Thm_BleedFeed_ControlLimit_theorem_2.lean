-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_theorem_2
-- name    : BleedFeed.ControlLimit.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:40.536098+00:00
-- url     : https://prove2.me/theorems/a64d04fe-2adb-4e22-b4c7-8d39fb45fd7f
-- title:
--   Theorem 2, p. 16 — under Condition (5) and Assumption 1, a growth-rate-based control limit $\mu^*(i,n)$
-- statement:
--   In the bleed–feed model (see the definition file), assume Condition (5) (on the range $\tilde\imath_{\mu^+}<i<I$) and Assumption 1. Then for every age $i<I$ and bleed–feed count $n\in\{0,\dots,N\}$ there is a real number $\mu^*(i,n)$ such that for every $\mu\in\mathcal M$:
--   $$
--   \mu<\mu^*(i,n)\ \Longrightarrow\ \text{continuing is optimal in }(i,\mu,n),\qquad \mu>\mu^*(i,n)\ \Longrightarrow\ \text{bleed–feed is optimal in }(i,\mu,n).
--   $$
--
--   For a given age and count, faster cultures should be bleed–fed and slower ones continued: a higher growth rate means a higher risk of missing the bleed–feed opportunity.
--
--   **Formalization Note** (a) The page states "for $\mu\le\mu^*(i,n)$ it is optimal to continue". Since $\mathcal M$ is a continuum and $\nu$ may jump, the set of rates where continuing is optimal can be half-open, $[\mu_\ell,\mu_0)$, with bleed–feed strictly optimal at $\mu_0$; then no $\mu^*$ satisfies the non-strict form. The statement therefore leaves the decision at $\mu=\mu^*$ itself unconstrained. (b) Condition (5) is on the corrected range and Assumption 1, the standing assumption of §4.2, is a hypothesis, as in Propositions 3 and 4.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 16, Theorem 2

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Theorem 2, p. 16: under Condition (5) (on the range ĩ_{µ⁺} < i < I) and Assumption 1, for
fixed i < I and n ∈ {0, …, N} there is a threshold µ*(i, n) such that for µ ∈ ℳ, continuing is
optimal when µ < µ*(i, n) and bleed–feed is optimal when µ > µ*(i, n). -/
theorem theorem_2 (P : Params) (hS : P.Standing) (h5 : Condition5 P) (hA1 : Assumption1 P) :
    ∀ i < P.I, ∀ n ≤ P.N, ∃ μStar : ℝ, ∀ μ ∈ P.rates,
      (μ < μStar → ContOpt P i μ n) ∧ (μStar < μ → BleedOpt P i μ n) := by sorry

end BleedFeed.ControlLimit
