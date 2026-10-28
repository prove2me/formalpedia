-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:39.83479+00:00
-- url     : https://prove2.me/theorems/81ad2591-daeb-4dec-b2fa-cf8b50f61aa5
-- title:
--   Selected-floor prefix certificate for prepared pair 1, right list, part 0
-- statement:
--   For prepared pair 1, right list, part 0, the selected-floor certificate succeeds for at most `34` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 138 through 171, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight1_001Part00.lean, lines 7-11, SHA-256 83c0961fbe73e281e5732b479f49c2104aa05bc48a41cfff3aae804a3e6101a3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 34
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
