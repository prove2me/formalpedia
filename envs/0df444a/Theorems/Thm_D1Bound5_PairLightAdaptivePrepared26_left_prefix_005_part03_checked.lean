-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_005_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:20.976908+00:00
-- url     : https://prove2.me/theorems/826929a2-e9bd-41e6-b320-79b08e0912e6
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 3
-- statement:
--   For prepared pair 26, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 372 through 383; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_005Part03.lean, lines 7-11, SHA-256 6ed100d3f8fbc39f2837358917299550d93c08456b71f9034c059c835b49bc5c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached005.drop 36) (leftRows005.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
