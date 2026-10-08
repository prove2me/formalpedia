-- Prove2me | Theorems.Thm_CarryRNG_SWB_periodic_after_r
-- name    : CarryRNG.SWB.periodic_after_r
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:35.066647+00:00
-- url     : https://prove2.me/theorems/330139b9-2e7c-4631-8a58-cb7bd52b5aa0
-- title:
--   p. 472 — every orbit enters a cycle within r steps
-- statement:
--   For every base $b\ge2$, lags $0<s<r$, and Method 1 seed $z$, the state reached after $r$ steps is periodic under the same step map:
--   $$f^r(z)\in\operatorname{PeriodicPts}(f).$$
--   Equivalently, the initial transient has length at most $r$. This is the paper’s explicit bound on when the periodic cycle begins; it includes the two trivial seeds.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5

import Definitions.Def_CarryRNG_SWB_step

namespace CarryRNG.SWB

/-- Page 472: the orbit is strictly periodic after at most `r` steps. -/
theorem periodic_after_r (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    (step b L hb)^[L.r] z ∈ Function.periodicPts (step b L hb) := by sorry

end CarryRNG.SWB
