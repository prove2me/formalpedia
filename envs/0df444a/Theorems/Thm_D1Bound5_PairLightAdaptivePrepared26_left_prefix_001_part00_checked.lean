-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:27.957109+00:00
-- url     : https://prove2.me/theorems/24afa67a-a763-4af0-b5be-5289d85f6bd4
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 0
-- statement:
--   For prepared pair 26, left list, part 0, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 54 through 56; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_001Part00.lean, lines 7-11, SHA-256 295bd3aef7475177e7163b2c2b53e03207128db15bce5d85c15adec021b07640. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
