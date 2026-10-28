-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_003_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_003_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:14.47986+00:00
-- url     : https://prove2.me/theorems/38448a3d-0480-4fe1-a375-9040ad4f5116
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 4
-- statement:
--   For prepared pair 26, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 226 through 237; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_003Part04.lean, lines 7-11, SHA-256 af9d5922a0a7b8c520cb2f3c1fef77ecc6c27b88ee85b72cb652f28d000c2914. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_003_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached003.drop 48) (rightRows003.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
