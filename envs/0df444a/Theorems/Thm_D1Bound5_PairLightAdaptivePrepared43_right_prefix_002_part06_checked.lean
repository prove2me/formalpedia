-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:41.789002+00:00
-- url     : https://prove2.me/theorems/8326baac-36fa-4b09-9462-098b675082c4
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 6
-- statement:
--   For prepared pair 43, right list, part 6, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 358 through 381, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_002Part06.lean, lines 9-14, SHA-256 9a755f01e06a0d2e5aa7a85e704c29700875474600a6f76d268580561e1dc656. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_part06_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.rightCached.drop 358)
      (PairLightPrepared43.rightRows.drop 358) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
