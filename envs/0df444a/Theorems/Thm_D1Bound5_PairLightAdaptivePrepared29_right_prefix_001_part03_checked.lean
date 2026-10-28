-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:50.783919+00:00
-- url     : https://prove2.me/theorems/570779fe-3e3a-40df-a731-ff4bbac691b6
-- title:
--   Selected-floor prefix certificate for prepared pair 29, right list, part 3
-- statement:
--   For prepared pair 29, right list, part 3, the selected-floor certificate succeeds for at most `108` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 273 through 380, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight29_001Part03.lean, lines 7-11, SHA-256 ee5bfc6148856cf5a9d75741422fdef2742168257d4248cf4f2416d6f8af4966. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 108
      (rightCached001.drop 148) (rightRows001.drop 148) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
