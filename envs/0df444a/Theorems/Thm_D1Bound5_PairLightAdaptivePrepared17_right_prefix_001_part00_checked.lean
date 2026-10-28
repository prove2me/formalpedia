-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:10.837832+00:00
-- url     : https://prove2.me/theorems/30e6664e-b529-4473-883e-57f7c53125e8
-- title:
--   Selected-floor prefix certificate for prepared pair 17, right list, part 0
-- statement:
--   For prepared pair 17, right list, part 0, the selected-floor certificate succeeds for at most `51` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 138 through 188; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight17_001Part00.lean, lines 7-11, SHA-256 a14a62b5d451c64fc5fc602db1669b1ce7daa05fca9118f2a8b841957f4ff4ac. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 51
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
