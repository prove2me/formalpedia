-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:40.76203+00:00
-- url     : https://prove2.me/theorems/f74d8c2c-f4d9-4854-95b7-2cc3c9dd4cf4
-- title:
--   Selected-floor prefix certificate for prepared pair 40, right list
-- statement:
--   For prepared pair 40, right list, the selected-floor certificate succeeds for at most `220` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Heads 138 through 357; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight40_001.lean, lines 7-11, SHA-256 44282c86bf1c59ec4421d35b907cad96c23cfbb059b97c262753152cada8eb95. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 220
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
