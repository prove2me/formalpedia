-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:45.397991+00:00
-- url     : https://prove2.me/theorems/04a3b489-cda6-4369-9865-1cbd346e9962
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 6
-- statement:
--   For prepared pair 14, right list, part 6, the selected-floor certificate succeeds for at most `7` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 489 through 495, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_003Part06.lean, lines 10-14, SHA-256 dae566eda82eb3b8b4b972bd91c144278331156ccb4e3094703f27c3265f8d94. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part06_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 7
      (PairLightPrepared14.rightCached.drop 489) (PairLightPrepared14.rightRows.drop 489) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
