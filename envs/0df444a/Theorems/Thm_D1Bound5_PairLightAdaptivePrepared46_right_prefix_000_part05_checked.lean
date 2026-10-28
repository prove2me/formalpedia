-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:37.04768+00:00
-- url     : https://prove2.me/theorems/04553c89-e113-47b9-8d14-7ccb0202058f
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list, part 5
-- statement:
--   For prepared pair 46, right list, part 5, the selected-floor certificate succeeds for at most `30` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 108 through 137, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_000Part05.lean, lines 7-11, SHA-256 32665e265709b538f8a241a50267301ff628b8787513d2f08737b6f1df679922. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 30
      (rightCached000.drop 108) (rightRows000.drop 108) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
