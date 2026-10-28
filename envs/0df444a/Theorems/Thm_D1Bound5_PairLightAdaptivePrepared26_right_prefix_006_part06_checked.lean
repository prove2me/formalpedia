-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:27.068216+00:00
-- url     : https://prove2.me/theorems/2a1196f2-f748-46d5-8ad3-163a8d4e6794
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 6
-- statement:
--   For prepared pair 26, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 515 through 526; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_006Part06.lean, lines 7-11, SHA-256 b6fc14a5a400510760feb5d997f7a7556052750d8762ea2b5600e5883a7623c4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached006.drop 72) (rightRows006.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
