-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:21.854081+00:00
-- url     : https://prove2.me/theorems/c8bcde9a-71d7-4d3e-95a8-12110c597986
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 9
-- statement:
--   For prepared pair 43, right list, part 9, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 430 through 453, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_002Part09.lean, lines 9-14, SHA-256 b978323fc44287ec8367d75ace79a378a7ddd2ccee2f4967f16890dcfc018944. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_part09_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.rightCached.drop 430)
      (PairLightPrepared43.rightRows.drop 430) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
