-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_007_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:52.75054+00:00
-- url     : https://prove2.me/theorems/29901fab-4e9d-44e0-a67d-dd73458a4200
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 3
-- statement:
--   For prepared pair 26, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 652 through 663; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_007Part03.lean, lines 7-11, SHA-256 984888a7cee5ca5b0fae94c885ef873054a623df4d29edf1cb154d0ebe6daa81. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_007_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached007.drop 36) (rightRows007.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
