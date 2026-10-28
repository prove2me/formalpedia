-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:34.591375+00:00
-- url     : https://prove2.me/theorems/0f290e2b-be1b-4ca8-b12d-522f210e65c2
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 5
-- statement:
--   For prepared pair 5, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 60 through 71, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_000Part05.lean, lines 11-16, SHA-256 9cc5ee7b9a615a47446398fa539911307dbb48442ef178fdd7fb3dfb26e1ca11. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 12
      (PairLightPrepared5.rightCached.drop 60)
      (PairLightPrepared5.rightRows.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
