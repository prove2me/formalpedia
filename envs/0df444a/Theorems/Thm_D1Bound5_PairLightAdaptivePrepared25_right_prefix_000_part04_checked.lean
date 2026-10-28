-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:17.290551+00:00
-- url     : https://prove2.me/theorems/28ad981d-0ed4-4f9c-abc1-cded237ae863
-- title:
--   Selected-floor prefix certificate for prepared pair 25, right list, part 4
-- statement:
--   For prepared pair 25, right list, part 4, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 109 through 124, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight25_000Part04.lean, lines 7-11, SHA-256 561fe2579a75e74b6966e38217bf24d04ffbe9b5e118c4884973b07c3c13bc4f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 16
      (rightCached000.drop 109) (rightRows000.drop 109) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
