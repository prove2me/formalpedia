-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_right_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.right_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:07.871053+00:00
-- url     : https://prove2.me/theorems/382cfbd7-0065-4e56-a199-9bc569894808
-- title:
--   Selected-floor prefix certificate for prepared pair 29, right list, part 2
-- statement:
--   For prepared pair 29, right list, part 2, the selected-floor certificate succeeds for at most `64` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 209 through 272, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight29_001Part02.lean, lines 7-11, SHA-256 0ee711a0da53ff9b2779f0b3acb4fc416ff7986211bcfd03b4988f2599b47fa5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.right_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 64
      (rightCached001.drop 84) (rightRows001.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
