-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:25.363155+00:00
-- url     : https://prove2.me/theorems/498e1375-b152-4e31-9246-eb1b76510807
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list
-- statement:
--   For prepared pair 24, right list, the selected-floor certificate succeeds for at most `198` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight24Prefix002.lean, lines 16-69, SHA-256 2a51e10d60081a9443e475442f374f15be52c35622f067ce0b15c421e9529173. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 198
      (PairLightPrepared24.rightCached.drop 248) (PairLightPrepared24.rightRows.drop 248) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared24
end
