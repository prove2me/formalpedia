-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared9_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared9.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:36:28.990312+00:00
-- url     : https://prove2.me/theorems/b5371033-3677-477e-83a7-2b4e34f1f437
-- title:
--   Selected-floor prefix certificate for prepared pair 9, left list
-- statement:
--   For prepared pair 9, left list, the selected-floor certificate succeeds for at most `219` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared9.sieve`. Heads 0 through 218; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft9_000.lean, lines 7-11, SHA-256 11233cdd41677ecb6e7f6dd7adf4910778aa786d8dd0a2b15ee910d03c5b3081. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData9_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared9.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared9.sieve 219
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared9
end
