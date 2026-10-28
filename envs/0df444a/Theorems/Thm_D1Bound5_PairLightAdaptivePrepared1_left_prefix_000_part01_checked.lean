-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:36.307639+00:00
-- url     : https://prove2.me/theorems/e0f00a01-0147-47b4-b85f-fc4e12b41af4
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list, part 1
-- statement:
--   For prepared pair 1, left list, part 1, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 16 through 35, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_000Part01.lean, lines 7-11, SHA-256 b5df000b8e8480eb1324abb271b7edc7808716b7d39346c9f9ea1e8023dc8951. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 20
      (leftCached000.drop 16) (leftRows000.drop 16) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
