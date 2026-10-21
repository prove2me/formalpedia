-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_theorem_1
-- name    : BleedFeed.ControlLimit.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:36.819991+00:00
-- url     : https://prove2.me/theorems/ce9a507f-d146-420e-bc77-148561e85353
-- title:
--   Theorem 1, p. 14 — under Condition (4), an age-based control limit $i^*(\mu,n)$
-- statement:
--   In the bleed–feed model (see the definition file), assume Condition (4). Then for every growth rate $\mu\in\mathcal M$ and bleed–feed count $n\in\{0,\dots,N\}$ there is an integer $i^*(\mu,n)$ such that for every age $i<I$:
--   $$
--   i\le i^*(\mu,n)\ \Longrightarrow\ \text{continuing is optimal in }(i,\mu,n),\qquad i>i^*(\mu,n)\ \Longrightarrow\ \text{bleed–feed is optimal in }(i,\mu,n).
--   $$
--
--   "Continuing is optimal" means $B(n)\le C(i,\mu,n)$ and "bleed–feed is optimal" means $n<N$ and $C(i,\mu,n)\le B(n)$, i.e. the action attains the maximum in the optimality equation (2). The theorem is a cultivation-age-based control limit: for a given culture, bleed–feed once it is old enough, and continue before.
--
--   **Formalization Note** The threshold is an integer so that $i^*(\mu,n)=-1$ (bleed–feed optimal at every age) is allowed.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 14, Theorem 1

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Theorem 1, p. 14: under Condition (4), for fixed µ ∈ ℳ and n ∈ {0, …, N} there is an integer
threshold i*(µ, n) such that for ages i < I, continuing is optimal when i ≤ i*(µ, n) and
bleed–feed is optimal when i > i*(µ, n). -/
theorem theorem_1 (P : Params) (hS : P.Standing) (h4 : Condition4 P) :
    ∀ μ ∈ P.rates, ∀ n ≤ P.N, ∃ iStar : ℤ, ∀ i < P.I,
      ((i : ℤ) ≤ iStar → ContOpt P i μ n) ∧ (iStar < i → BleedOpt P i μ n) := by sorry

end BleedFeed.ControlLimit
