-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:37.632908+00:00
-- url     : https://prove2.me/theorems/bd333c31-2243-4ecd-8bfd-9577b410f677
-- title:
--   Selected-floor prefix certificate for prepared pair 11, right list, part 0
-- statement:
--   For prepared pair 11, right list, part 0, the selected-floor certificate succeeds for at most `34` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 138 through 171, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight11_001Part00.lean, lines 7-11, SHA-256 4d8668162c61d57e74b08e2482a65de8b650d98c9128c831f3ca74d4abdd21c8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 34
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
