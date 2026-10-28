-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_right_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared45.right_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:30.946529+00:00
-- url     : https://prove2.me/theorems/65b78d83-a8d7-4f17-b619-d667058b1571
-- title:
--   Selected-floor prefix certificate for prepared pair 45, right list
-- statement:
--   For prepared pair 45, right list, the selected-floor certificate succeeds for at most `103` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 5, and the sieve is `PairLightPrepared45.sieve`. Heads 103 through 205; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight45_002.lean, lines 7-11, SHA-256 eaa071f2b38edad14d61fd744bb6f22b6c1f2721c90d54df65b3ea523bfaca4a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData45_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared45.right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 5 PairLightPrepared45.sieve 103
      rightCached002 rightRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared45
end
