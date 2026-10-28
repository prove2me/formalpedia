-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared45.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:40:25.190029+00:00
-- url     : https://prove2.me/theorems/067ad2c5-3f53-43a6-9332-98dd821676dc
-- title:
--   Selected-floor prefix certificate for prepared pair 45, left list
-- statement:
--   For prepared pair 45, left list, the selected-floor certificate succeeds for at most `61` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 5, and the sieve is `PairLightPrepared45.sieve`. Heads 43 through 103; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft45_001.lean, lines 7-11, SHA-256 7785376f80f3cd1279e75ef9677e841a9d37597e3225336b33d0215bad4d16a0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData45_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared45.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 5 PairLightPrepared45.sieve 61
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared45
end
