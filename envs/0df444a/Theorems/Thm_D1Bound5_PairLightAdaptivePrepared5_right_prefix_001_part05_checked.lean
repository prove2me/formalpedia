-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:19.917248+00:00
-- url     : https://prove2.me/theorems/a8cd1c10-3bdd-4708-8d30-4c26785239ed
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 5
-- statement:
--   For prepared pair 5, right list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 226 through 249, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_001Part05.lean, lines 11-16, SHA-256 bb78612f9b724ce426e6771865c53ce5695d84d5df86fe60298ff47774e10814. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.rightCached.drop 226)
      (PairLightPrepared5.rightRows.drop 226) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
