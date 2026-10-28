-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_003_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:50.103094+00:00
-- url     : https://prove2.me/theorems/71d0aae9-f456-432f-b157-f15a05141a68
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 3
-- statement:
--   For prepared pair 26, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 214 through 225; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_003Part03.lean, lines 7-11, SHA-256 b3f69b6cce6bae2eca5baa7ea37414d593c64b2f57b9bdc11f75e32a7f33a3f1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached003.drop 36) (leftRows003.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
