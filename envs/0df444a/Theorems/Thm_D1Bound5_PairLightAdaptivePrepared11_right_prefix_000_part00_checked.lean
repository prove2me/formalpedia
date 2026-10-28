-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.right_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:10.520333+00:00
-- url     : https://prove2.me/theorems/68fa7a78-624c-4ca2-9ffa-bf3519aeb84e
-- title:
--   Selected-floor prefix certificate for prepared pair 11, right list, part 0
-- statement:
--   For prepared pair 11, right list, part 0, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 0 through 15, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight11_000Part00.lean, lines 7-11, SHA-256 8facdd924e0aa2ab88bb9e8535873ab3a1025ff73ef9d8ff40257889796be97c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.right_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 16
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
