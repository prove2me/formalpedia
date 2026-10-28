-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:22.096411+00:00
-- url     : https://prove2.me/theorems/a42083d2-2388-40bf-a2f9-794e0a45d329
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list, part 5
-- statement:
--   For prepared pair 46, left list, part 5, the selected-floor certificate succeeds for at most `29` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 108 through 136, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_000Part05.lean, lines 7-11, SHA-256 51bebc004aec7a0f33677d28187845e45de0fb3ee718fdd100a57e6f2fde0d38. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 29
      (leftCached000.drop 108) (leftRows000.drop 108) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
