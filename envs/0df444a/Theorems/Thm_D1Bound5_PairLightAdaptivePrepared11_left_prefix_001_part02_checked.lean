-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:07.254093+00:00
-- url     : https://prove2.me/theorems/01d306d5-4ad0-48dc-8df6-21d5d0b46b19
-- title:
--   Selected-floor prefix certificate for prepared pair 11, left list, part 2
-- statement:
--   For prepared pair 11, left list, part 2, the selected-floor certificate succeeds for at most `56` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 214 through 269, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft11_001Part02.lean, lines 7-11, SHA-256 b04e9d9e7b8eb374b46812ff3811ab637c8f9ef2320214c5bb93ff36b3aa6c3a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 56
      (leftCached001.drop 76) (leftRows001.drop 76) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
