-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:27.067595+00:00
-- url     : https://prove2.me/theorems/42e11881-7925-4535-a710-87cf0afbb944
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list, part 3
-- statement:
--   For prepared pair 1, left list, part 3, the selected-floor certificate succeeds for at most `91` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 269 through 359, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_001Part03.lean, lines 7-11, SHA-256 c13cbdbaf6250b057bb174db521f5a5c765a6ca0a3b3dc8a383a734b542ee302. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 91
      (leftCached001.drop 132) (leftRows001.drop 132) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
