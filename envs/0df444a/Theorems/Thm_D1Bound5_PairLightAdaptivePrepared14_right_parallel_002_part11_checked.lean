-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part11_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:49.077229+00:00
-- url     : https://prove2.me/theorems/21ddffb8-9bf7-4ea4-a4bc-915aa5bb6109
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 11
-- statement:
--   For prepared pair 14, right list, part 11, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 334 through 345, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_002Part11.lean, lines 10-14, SHA-256 3881015f394dd2447aac0bd5c4f2c9e0bd7a2d0373d1850871af04061dfde0db. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part11_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 334) (PairLightPrepared14.rightRows.drop 334) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
