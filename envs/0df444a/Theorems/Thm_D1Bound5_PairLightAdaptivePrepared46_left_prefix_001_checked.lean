-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:55.202644+00:00
-- url     : https://prove2.me/theorems/50fedd55-cac5-4bf1-b603-49fa8041a852
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list
-- statement:
--   For prepared pair 46, left list, the selected-floor certificate succeeds for at most `223` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Heads 137 through 359; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_001.lean, lines 12-36, SHA-256 53fcefbac060778d76cd3a0ec795a4b7706f12fac4304f4ad763959f7803865d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 223
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
