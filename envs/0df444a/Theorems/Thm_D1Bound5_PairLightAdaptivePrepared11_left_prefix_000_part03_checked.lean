-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:47.98667+00:00
-- url     : https://prove2.me/theorems/b6a94b8e-ea64-417d-9840-465f5424a453
-- title:
--   Selected-floor prefix certificate for prepared pair 11, left list, part 3
-- statement:
--   For prepared pair 11, left list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 58 through 81, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft11_000Part03.lean, lines 7-11, SHA-256 293a71d484f5859d305c3004fcf794c68ffd046e5ded927d181f49b0b5323657. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 24
      (leftCached000.drop 58) (leftRows000.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
