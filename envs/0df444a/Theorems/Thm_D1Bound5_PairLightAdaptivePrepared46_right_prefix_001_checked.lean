-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:02.132072+00:00
-- url     : https://prove2.me/theorems/bdb2a4df-29e5-44e5-bdf0-80d7de562038
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list
-- statement:
--   For prepared pair 46, right list, the selected-floor certificate succeeds for at most `220` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Heads 138 through 357; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_001.lean, lines 12-36, SHA-256 a868cddbc4770670c4125016886a5df3cf9fb2e3cab453def24500d0af800a52. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 220
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
