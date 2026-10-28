-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:23.962793+00:00
-- url     : https://prove2.me/theorems/96daecde-742a-43ec-a0b4-03ae14070a66
-- title:
--   Selected-floor prefix certificate for prepared pair 48, right list, part 0
-- statement:
--   For prepared pair 48, right list, part 0, the selected-floor certificate succeeds for at most `51` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 138 through 188; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight48_001Part00.lean, lines 7-11, SHA-256 e126280dcb6d6d6cdfae1cd4aa30b58d4dad1a3d9a73d85bad9dbf4e93f469a7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 51
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
