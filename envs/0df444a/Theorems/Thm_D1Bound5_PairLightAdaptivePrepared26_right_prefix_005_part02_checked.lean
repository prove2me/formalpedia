-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_005_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_005_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:38.732992+00:00
-- url     : https://prove2.me/theorems/70516367-58d6-4efd-9d23-e027b0496a7c
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 2
-- statement:
--   For prepared pair 26, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 360 through 371; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_005Part02.lean, lines 7-11, SHA-256 d36017dcf77c4e323a2bd03f607ad4b3d2cae32a73b0dde3432fe4c8887228d9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_005_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached005.drop 24) (rightRows005.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
