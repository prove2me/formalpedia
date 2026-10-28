-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_003_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_003_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:11.892069+00:00
-- url     : https://prove2.me/theorems/9634eaee-01b9-44a3-88b0-64d78b06e927
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 0
-- statement:
--   For prepared pair 26, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 178 through 189; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_003Part00.lean, lines 7-11, SHA-256 2b18fa3f19d878b064c5b40c7b4a86003cd46493bd3d03886e1c4dbcd6144a49. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_003_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached003.drop 0) (rightRows003.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
