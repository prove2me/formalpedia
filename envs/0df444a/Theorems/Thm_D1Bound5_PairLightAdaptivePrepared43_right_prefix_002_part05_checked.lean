-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:46.504988+00:00
-- url     : https://prove2.me/theorems/bdf0f05c-9190-4c0b-977b-54a7f1a8ef97
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 5
-- statement:
--   For prepared pair 43, right list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 334 through 357, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_002Part05.lean, lines 9-14, SHA-256 bef8cc8e7710b5fb56873fbe3a69fae2b6860a4edf90a33df3ef678193991142. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.rightCached.drop 334)
      (PairLightPrepared43.rightRows.drop 334) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
