-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:36.758695+00:00
-- url     : https://prove2.me/theorems/c4f4d9de-5401-4c26-85d7-c93225cc3740
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 4
-- statement:
--   For prepared pair 43, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 140 through 151, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_001Part04.lean, lines 9-14, SHA-256 30d5238bc81d5770b6322ce18a43c52977ae8af14a15632d42a2f7005ae28ae4. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 140)
      (PairLightPrepared43.rightRows.drop 140) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
