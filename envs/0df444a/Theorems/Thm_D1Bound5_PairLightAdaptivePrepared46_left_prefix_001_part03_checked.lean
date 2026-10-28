-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:17.835164+00:00
-- url     : https://prove2.me/theorems/e8e5d975-3a70-42ef-a9f6-01c1a8889af7
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list, part 3
-- statement:
--   For prepared pair 46, left list, part 3, the selected-floor certificate succeeds for at most `91` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 269 through 359, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_001Part03.lean, lines 7-11, SHA-256 3eb0ca94942d8fcba0982e9decd43f8a82d85878edaafcc7bbb447066a761bc1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 91
      (leftCached001.drop 132) (leftRows001.drop 132) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
