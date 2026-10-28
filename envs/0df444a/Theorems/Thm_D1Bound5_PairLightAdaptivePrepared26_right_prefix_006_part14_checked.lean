-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:52.491999+00:00
-- url     : https://prove2.me/theorems/012ceb67-0b46-404d-b687-ef72b64cf6f5
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 14
-- statement:
--   For prepared pair 26, right list, part 14, the selected-floor certificate succeeds for at most `5` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 611 through 615; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_006Part14.lean, lines 7-11, SHA-256 752deb4a0e84db23069f01261d3bdb186f7ea67fa57278da5fc9c71862741a5f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part14_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 5
      (rightCached006.drop 168) (rightRows006.drop 168) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
