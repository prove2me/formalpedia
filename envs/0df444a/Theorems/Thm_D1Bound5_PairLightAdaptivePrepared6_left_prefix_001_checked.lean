-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:34.898261+00:00
-- url     : https://prove2.me/theorems/20f73d69-71e0-42d1-a8b6-0151270b3d30
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list
-- statement:
--   For prepared pair 6, left list, the selected-floor certificate succeeds for at most `71` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_001.lean, lines 15-50, SHA-256 69c7e4d9c1f6696745881b1a2b963bc1dfa163b88cadf54552e32486de62ca51. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 71
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
