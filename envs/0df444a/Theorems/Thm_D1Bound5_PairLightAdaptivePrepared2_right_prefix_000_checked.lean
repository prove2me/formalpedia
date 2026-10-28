-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared2_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared2.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:10.650376+00:00
-- url     : https://prove2.me/theorems/49989bd7-7ce6-4760-bb7c-9fe3f388880a
-- title:
--   Selected-floor prefix certificate for prepared pair 2, right list
-- statement:
--   For prepared pair 2, right list, the selected-floor certificate succeeds for at most `207` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared2.sieve`. Heads 0 through 206; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight2_000.lean, lines 7-11, SHA-256 21461a85cc0732c28c1c0ea7b1365c041b6bed7c206b106448a3c933baee712b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData2_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared2.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared2.sieve 207
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared2
end
