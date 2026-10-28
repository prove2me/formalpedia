-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:55.761479+00:00
-- url     : https://prove2.me/theorems/dc57ee23-e83f-4c11-9313-fb7b51a3927d
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 2
-- statement:
--   For prepared pair 26, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 275 through 286; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_004Part02.lean, lines 7-11, SHA-256 f24892f9c7b9817c5cb7beed3e16cddd744fc7089a8899e69e36b287a3add203. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached004.drop 24) (rightRows004.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
