-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:07.920993+00:00
-- url     : https://prove2.me/theorems/6b6687d4-83a4-4f6f-9f06-2f8a3f75621a
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 7
-- statement:
--   For prepared pair 43, right list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 176 through 187, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_001Part07.lean, lines 9-14, SHA-256 58f2371e6fe7cbb8b4bb78cd9ffa8ccf9d5c2dfa006c947222b360cc3baeff63. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part07_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 176)
      (PairLightPrepared43.rightRows.drop 176) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
