-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_006_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:35.780825+00:00
-- url     : https://prove2.me/theorems/463d7db7-ba78-4df6-b99b-423214e03d23
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 14
-- statement:
--   For prepared pair 26, left list, part 14, the selected-floor certificate succeeds for at most `5` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 611 through 615; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_006Part14.lean, lines 7-11, SHA-256 7aeb0204cce4652d2ca015191ac04eefc0869b1fbd451256cff828cd8bae0aac. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part14_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 5
      (leftCached006.drop 168) (leftRows006.drop 168) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
