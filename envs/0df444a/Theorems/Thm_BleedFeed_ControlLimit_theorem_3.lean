-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_theorem_3
-- name    : BleedFeed.ControlLimit.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:13.892988+00:00
-- url     : https://prove2.me/theorems/1ec808ba-45c0-42dd-a225-c7a42c53a446
-- title:
--   Theorem 3, p. 16 — a control limit $n^*(i,\mu)$ in the bleed–feed count
-- statement:
--   In the bleed–feed model (see the definition file), for every age $i<I$ and growth rate $\mu\in\mathcal M$ there is an integer $n^*(i,\mu)$ such that for every $n\in\{0,\dots,N\}$:
--   $$
--   n\le n^*(i,\mu)\ \Longrightarrow\ \text{bleed–feed is optimal in }(i,\mu,n),\qquad n>n^*(i,\mu)\ \Longrightarrow\ \text{continuing is optimal in }(i,\mu,n).
--   $$
--
--   When only a few bleed–feeds have been performed the decision-maker should bleed–feed; close to the regulatory limit $N$ it should continue. No condition on the model is needed.
--
--   **Formalization Note** The page writes the second clause as "$n>n^*(i,n)$" and names the limit "$n^*(i,n)$"; both are typos for $n^*(i,\mu)$. The threshold is an integer so that $n^*(i,\mu)=-1$ (continuing optimal for every count) is allowed.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 16, Theorem 3

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Theorem 3, p. 16: for fixed i < I and µ ∈ ℳ there is an integer threshold n*(i, µ) such that
for n ∈ {0, …, N}, bleed–feed is optimal when n ≤ n*(i, µ) and continuing is optimal when
n > n*(i, µ). -/
theorem theorem_3 (P : Params) (hS : P.Standing) :
    ∀ i < P.I, ∀ μ ∈ P.rates, ∃ nStar : ℤ, ∀ n ≤ P.N,
      ((n : ℤ) ≤ nStar → BleedOpt P i μ n) ∧ (nStar < n → ContOpt P i μ n) := by sorry

end BleedFeed.ControlLimit
