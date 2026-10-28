-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:08.520588+00:00
-- url     : https://prove2.me/theorems/4754ec7b-5dbd-442a-b665-e033037d20a6
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 10
-- statement:
--   For prepared pair 43, right list, part 10, the selected-floor certificate succeeds for at most `2` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 212 through 213, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_001Part10.lean, lines 9-14, SHA-256 0f5b3cc4b76c66950a7dfbc4e342d3799a8475764b4e2bde54b8ad87dd01bda7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part10_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 2
      (PairLightPrepared43.rightCached.drop 212)
      (PairLightPrepared43.rightRows.drop 212) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
