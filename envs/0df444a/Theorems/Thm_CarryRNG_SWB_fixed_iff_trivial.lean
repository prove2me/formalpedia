-- Prove2me | Theorems.Thm_CarryRNG_SWB_fixed_iff_trivial
-- name    : CarryRNG.SWB.fixed_iff_trivial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:42.110204+00:00
-- url     : https://prove2.me/theorems/326747f5-311e-4e35-9fe2-f269100f6ad5
-- title:
--   p. 472 — precisely two fixed seeds
-- statement:
--   Fix $b\ge2$ and lags $0<s<r$. A Method 1 state is unchanged by one subtract-with-borrow step if and only if it is one of the two trivial seeds:
--   $$
--   f(x_1,\ldots,x_r,c)=(x_1,\ldots,x_r,c)
--   \quad\Longleftrightarrow\quad
--   (x_1,\ldots,x_r,c)=(0,\ldots,0,0)\ \text{or}\ (b-1,\ldots,b-1,1).
--   $$
--   This identifies the two period-one exceptions to the order-of-base claim.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5

import Definitions.Def_CarryRNG_SWB_step
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

namespace CarryRNG.SWB

/-- Page 472: Method 1 has precisely the two stated fixed seeds. -/
theorem fixed_iff_trivial (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    step b L hb z = z ↔ z = CarryRNG.AWC.zeroSeed b L.r hb ∨ z = CarryRNG.AWC.topSeed b L.r hb := by sorry

end CarryRNG.SWB
