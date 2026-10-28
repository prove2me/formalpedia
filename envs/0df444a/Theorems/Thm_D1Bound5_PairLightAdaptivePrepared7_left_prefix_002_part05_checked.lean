-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:41.717861+00:00
-- url     : https://prove2.me/theorems/2774e26e-a979-479e-a128-07f373b87c84
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 5
-- statement:
--   For prepared pair 7, left list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 388 through 411, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_002Part05.lean, lines 11-16, SHA-256 445c1e853685b443dbd0c4824e111baf891a8141bc0fbbd91d6315d4aeb6e5d9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.leftCached.drop 388)
      (PairLightPrepared7.leftRows.drop 388) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
