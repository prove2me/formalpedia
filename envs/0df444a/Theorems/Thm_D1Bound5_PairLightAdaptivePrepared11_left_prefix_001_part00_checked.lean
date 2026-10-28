-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:48.383723+00:00
-- url     : https://prove2.me/theorems/93e60ffd-feca-4234-ae61-b604c111163e
-- title:
--   Selected-floor prefix certificate for prepared pair 11, left list, part 0
-- statement:
--   For prepared pair 11, left list, part 0, the selected-floor certificate succeeds for at most `34` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 138 through 171, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft11_001Part00.lean, lines 7-11, SHA-256 44601b9ade9fb7d33e6bc94eae5fe308ba707dbe0b5f91fd4a5b13fd5a8bae10. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 34
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
