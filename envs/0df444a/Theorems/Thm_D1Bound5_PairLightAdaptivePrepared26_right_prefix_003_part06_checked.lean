-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:32.660491+00:00
-- url     : https://prove2.me/theorems/6b872451-fb46-42a5-a5cd-d475b4269583
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 6
-- statement:
--   For prepared pair 26, right list, part 6, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 250 through 250; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_003Part06.lean, lines 7-11, SHA-256 f92c14608f96cf96e4d4a1ddbe1ab6dfe21ceeffbeeeac686ec407dadc1029dc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_003_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (rightCached003.drop 72) (rightRows003.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
