-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:17.238666+00:00
-- url     : https://prove2.me/theorems/33b0ee02-0433-460a-ba99-fb07dee01a82
-- title:
--   Selected-floor prefix certificate for prepared pair 17, right list, part 2
-- statement:
--   For prepared pair 17, right list, part 2, the selected-floor certificate succeeds for at most `93` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 265 through 357; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight17_001Part02.lean, lines 7-11, SHA-256 217dde5b6da2520c0892bde601ee32ecf7720506c2e1628773589ed2581401c1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 93
      (rightCached001.drop 127) (rightRows001.drop 127) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
