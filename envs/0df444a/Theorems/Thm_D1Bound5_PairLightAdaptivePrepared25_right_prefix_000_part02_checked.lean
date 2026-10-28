-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:45.095888+00:00
-- url     : https://prove2.me/theorems/ece3b09f-4b52-46a0-87d6-8a2282f2e994
-- title:
--   Selected-floor prefix certificate for prepared pair 25, right list, part 2
-- statement:
--   For prepared pair 25, right list, part 2, the selected-floor certificate succeeds for at most `28` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 50 through 77, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight25_000Part02.lean, lines 7-11, SHA-256 d5cefe38d4edb0024e7a7b3560c52275b95393b0d05af3112afd5052493f069a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 28
      (rightCached000.drop 50) (rightRows000.drop 50) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
