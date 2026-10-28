-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:36.354336+00:00
-- url     : https://prove2.me/theorems/8eac3851-d0bb-4155-86f9-61e9a1fffc43
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 1
-- statement:
--   For prepared pair 43, right list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 238 through 261, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_002Part01.lean, lines 9-14, SHA-256 1bbbb5eb08cf332580d6078a746f4eaa4f1affc596464c7b57d37c1780448511. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.rightCached.drop 238)
      (PairLightPrepared43.rightRows.drop 238) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
