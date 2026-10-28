-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared45.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:33.192811+00:00
-- url     : https://prove2.me/theorems/d58c7ef5-efd2-46db-87ac-a9d0926d3a58
-- title:
--   Selected-floor prefix certificate for prepared pair 45, left list
-- statement:
--   For prepared pair 45, left list, the selected-floor certificate succeeds for at most `101` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 5, and the sieve is `PairLightPrepared45.sieve`. Heads 104 through 204; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft45_002.lean, lines 7-11, SHA-256 c56573fceff3966f617715afaad599a7b9e22f5620dfdc1f5729f74a3d2f37e4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData45_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared45.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 5 PairLightPrepared45.sieve 101
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared45
end
