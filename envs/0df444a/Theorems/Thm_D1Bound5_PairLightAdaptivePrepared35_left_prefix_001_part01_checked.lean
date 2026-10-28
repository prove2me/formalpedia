-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:43.060665+00:00
-- url     : https://prove2.me/theorems/a075d18e-4ae4-47b3-9bde-eb75927ed3ef
-- title:
--   Selected-floor prefix certificate for prepared pair 35, left list, part 1
-- statement:
--   For prepared pair 35, left list, part 1, the selected-floor certificate succeeds for at most `62` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 178 through 239; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft35_001Part01.lean, lines 7-11, SHA-256 150a2adc34cfdf4753957a65fb67b167773e466b8dee512ab25afa1f06fd4d57. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 62
      (leftCached001.drop 46) (leftRows001.drop 46) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
