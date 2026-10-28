-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:29.812122+00:00
-- url     : https://prove2.me/theorems/3a5158e5-4ade-41ca-a21d-44a9902df81a
-- title:
--   Selected-floor prefix certificate for prepared pair 29, left list, part 3
-- statement:
--   For prepared pair 29, left list, part 3, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 78 through 108, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft29_000Part03.lean, lines 7-11, SHA-256 7f84ae1f458ac9a506f77712a20ff418a6ca4c9b62030327aa8f17e935d0f5db. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 31
      (leftCached000.drop 78) (leftRows000.drop 78) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
