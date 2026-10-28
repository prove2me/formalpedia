-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_005_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_005_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:26.70679+00:00
-- url     : https://prove2.me/theorems/3d5b39c4-ed71-49d0-bceb-350d02e75bbe
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 4
-- statement:
--   For prepared pair 26, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 384 through 395; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_005Part04.lean, lines 7-11, SHA-256 84c315feea381902f7ed3ae76339a19fbc92be2d586f269fb4e21e6e166656fe. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_005_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached005.drop 48) (rightRows005.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
