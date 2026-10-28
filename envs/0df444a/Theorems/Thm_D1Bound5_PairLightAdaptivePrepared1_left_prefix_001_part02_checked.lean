-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:37.343875+00:00
-- url     : https://prove2.me/theorems/124ca48c-37f6-41e5-aa4c-a0178d70f825
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list, part 2
-- statement:
--   For prepared pair 1, left list, part 2, the selected-floor certificate succeeds for at most `56` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 213 through 268, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_001Part02.lean, lines 7-11, SHA-256 a712f49bedc427688fdd3effce4d4262b287f031f3e49c8d33e13ed287fb0b59. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 56
      (leftCached001.drop 76) (leftRows001.drop 76) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
