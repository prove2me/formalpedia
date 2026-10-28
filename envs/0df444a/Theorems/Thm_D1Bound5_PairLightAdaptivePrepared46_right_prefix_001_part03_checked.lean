-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:35.587148+00:00
-- url     : https://prove2.me/theorems/e99c5cac-572d-478b-8efb-0de511479bdc
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list, part 3
-- statement:
--   For prepared pair 46, right list, part 3, the selected-floor certificate succeeds for at most `88` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 270 through 357, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_001Part03.lean, lines 7-11, SHA-256 073bcfff0d6586d2670bdd159014e8792ba68cd3f2c3b263744c7f3a8ad0c136. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 88
      (rightCached001.drop 132) (rightRows001.drop 132) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
