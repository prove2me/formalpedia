-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:44.442551+00:00
-- url     : https://prove2.me/theorems/9c08003d-f20b-4c7c-aa68-6fe4066d66a9
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list, part 0
-- statement:
--   For prepared pair 46, right list, part 0, the selected-floor certificate succeeds for at most `34` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 138 through 171, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_001Part00.lean, lines 7-11, SHA-256 b96fb556175990d5a50b7fd3d496b0b18e4fe7c11901293d6665456ad2588efe. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 34
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
