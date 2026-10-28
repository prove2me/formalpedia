-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:47.275251+00:00
-- url     : https://prove2.me/theorems/13ea133e-3c1e-4f8f-a433-4d1f08d8d37c
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 6
-- statement:
--   For prepared pair 5, right list, part 6, the selected-floor certificate succeeds for at most `22` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 250 through 271, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_001Part06.lean, lines 11-16, SHA-256 0ae087fdb621c0e7d6718f982ec570cdea8a08a5fa50a7b6cc59e9027d0d2385. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 22
      (PairLightPrepared5.rightCached.drop 250)
      (PairLightPrepared5.rightRows.drop 250) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
