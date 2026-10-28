-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared20_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared20.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:22.435703+00:00
-- url     : https://prove2.me/theorems/50ff911a-76c4-4f6e-baf2-8e3803128a7e
-- title:
--   Selected-floor prefix certificate for prepared pair 20, left list
-- statement:
--   For prepared pair 20, left list, the selected-floor certificate succeeds for at most `223` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared20.sieve`. Heads 0 through 222; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft20_000.lean, lines 7-11, SHA-256 3718cbe88081a035617096b55595109cab9198a56a2ea190037d0c198bfd7124. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData20_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared20.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared20.sieve 223
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared20
end
