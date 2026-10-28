-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_right_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.right_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:03.683789+00:00
-- url     : https://prove2.me/theorems/35e2604a-8481-4eb6-8536-dd85483d25e0
-- title:
--   Selected-floor prefix certificate for prepared pair 29, right list, part 4
-- statement:
--   For prepared pair 29, right list, part 4, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 109 through 124, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight29_000Part04.lean, lines 7-11, SHA-256 9b723bb5ca31a6a36a182a1357f05d3f1483878881f86e16a33adfaa299c352b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.right_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 16
      (rightCached000.drop 109) (rightRows000.drop 109) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
