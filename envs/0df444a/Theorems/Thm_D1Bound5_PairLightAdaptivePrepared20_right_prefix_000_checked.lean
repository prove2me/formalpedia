-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared20_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared20.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:50:13.798546+00:00
-- url     : https://prove2.me/theorems/0e75ca50-c142-423c-98f0-79d28a665814
-- title:
--   Selected-floor prefix certificate for prepared pair 20, right list
-- statement:
--   For prepared pair 20, right list, the selected-floor certificate succeeds for at most `223` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared20.sieve`. Heads 0 through 222; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight20_000.lean, lines 7-11, SHA-256 4b2f0c6e09dcd8a1ab3be40d36a413846952d344f3dbeccdff238706a5ea85f5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData20_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared20.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared20.sieve 223
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared20
end
