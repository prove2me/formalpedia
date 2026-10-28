-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part11_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_007_part11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:26.630587+00:00
-- url     : https://prove2.me/theorems/ddf65206-9143-468c-b046-3e68b3be69e5
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 11
-- statement:
--   For prepared pair 26, right list, part 11, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 748 through 759; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_007Part11.lean, lines 7-11, SHA-256 ac53129414466499d946b9ac152ea00f02d24c36c01c92e8ba40b1c2764d927a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_007_part11_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached007.drop 132) (rightRows007.drop 132) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
