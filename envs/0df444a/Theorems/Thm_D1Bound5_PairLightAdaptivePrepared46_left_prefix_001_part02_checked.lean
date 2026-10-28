-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:37.298668+00:00
-- url     : https://prove2.me/theorems/2d7a30dc-8a70-4652-8b64-4cf8f119da2c
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list, part 2
-- statement:
--   For prepared pair 46, left list, part 2, the selected-floor certificate succeeds for at most `56` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 213 through 268, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_001Part02.lean, lines 7-11, SHA-256 216500c4c3ef200ce1c8f9ccb854ecddf96c55627eecca314b2e986e59d7291b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 56
      (leftCached001.drop 76) (leftRows001.drop 76) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
