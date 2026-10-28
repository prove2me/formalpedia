-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_001_part16_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part16_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:04.562546+00:00
-- url     : https://prove2.me/theorems/aa6a4c96-32c8-4a5b-8b14-f23043ece14c
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 16
-- statement:
--   For prepared pair 26, left list, part 16, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 102 through 104; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_001Part16.lean, lines 7-11, SHA-256 3f868cd12033f73e68d730cf4228340ccc26a4520cac4dab68210af68c64326d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part16_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached001.drop 48) (leftRows001.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
