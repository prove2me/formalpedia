-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_proposition_6
-- name    : BleedFeed.ControlLimit.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:14.82171+00:00
-- url     : https://prove2.me/theorems/5672af3e-2bfa-41a4-9370-c888da0ef1cf
-- title:
--   Proposition 6, p. 16 — $C(i,\mu,n)-B(n)$ is nondecreasing in the bleed–feed count $n$
-- statement:
--   In the bleed–feed model (see the definition file), for every age $i<I$, every growth rate $\mu\in\mathcal M$ and every $n<N$,
--   $$
--   C(i,\mu,n)-B(n)\le C(i,\mu,n+1)-B(n+1).
--   $$
--
--   The advantage of continuing over bleed–feeding grows as bleed–feeds are used up: if continuing is optimal with $n$ bleed–feeds performed, it remains optimal with $n+1$. This yields the count threshold of Theorem 3; no condition on the model is needed.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 16, Proposition 6

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Proposition 6, p. 16: C(i, µ, n) − B(n) ≤ C(i, µ, n + 1) − B(n + 1) for all i < I, µ ∈ ℳ,
n < N. -/
theorem proposition_6 (P : Params) (hS : P.Standing) (i : ℕ) (hi : i < P.I) (μ : ℝ)
    (hμ : μ ∈ P.rates) (n : ℕ) (hn : n < P.N) :
    C P i μ n - B P n ≤ C P i μ (n + 1) - B P (n + 1) := by sorry

end BleedFeed.ControlLimit
