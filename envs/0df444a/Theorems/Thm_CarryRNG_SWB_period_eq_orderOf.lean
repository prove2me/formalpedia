-- Prove2me | Theorems.Thm_CarryRNG_SWB_period_eq_orderOf
-- name    : CarryRNG.SWB.period_eq_orderOf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:17.130908+00:00
-- url     : https://prove2.me/theorems/ed647a41-29d8-4fc0-8d6f-37f87adfafac
-- title:
--   §4.3 — nontrivial Method 1 period equals the order of b
-- statement:
--   Let $b\ge2$, $0<s<r$, and $m=b^r-b^s+1$ be prime. Starting from any state $z$ other than $(0,\ldots,0,0)$ or $(b-1,\ldots,b-1,1)$, let $f$ be the Method 1 subtract-with-borrow step. The state after the first $r$ steps has minimal positive period
--   $$
--   \operatorname{period}(f^r(z))=\operatorname{ord}_m(b).
--   $$
--   Thus every nontrivial seed enters, within at most $r$ steps, a cycle whose exact state period is the multiplicative order of the base modulo the paper’s Method 1 modulus. No primitive-root assumption is required.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), pp. 470–472, Sections 4.3 and 4.5

import Definitions.Def_CarryRNG_SWB_step
import Definitions.Def_CarryRNG_SWB_modulus
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

namespace CarryRNG.SWB

/-- Sections 4.3 and 4.5: every nontrivial Method 1 orbit has the order-of-base
period once its at-most-`r`-step transient has ended. -/
theorem period_eq_orderOf (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b)
    (hm : (modulus b L).Prime) (z : CarryRNG.AWC.State b L.r)
    (hzero : z ≠ CarryRNG.AWC.zeroSeed b L.r hb) (htop : z ≠ CarryRNG.AWC.topSeed b L.r hb) :
    Function.minimalPeriod (step b L hb) ((step b L hb)^[L.r] z) =
      orderOf (b : ZMod (modulus b L)) := by sorry

end CarryRNG.SWB
