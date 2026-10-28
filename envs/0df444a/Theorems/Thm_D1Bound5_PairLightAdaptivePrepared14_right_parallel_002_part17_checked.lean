-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part17_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part17_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:49.203767+00:00
-- url     : https://prove2.me/theorems/60601fb5-a232-4ad0-a111-d2fa9499a8d9
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 17
-- statement:
--   For prepared pair 14, right list, part 17, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 406 through 416, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_002Part17.lean, lines 10-14, SHA-256 15818d71f7c0b07363d866038e3f95c97c52d5c00dc46806318ea7362b1709cb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part17_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 11
      (PairLightPrepared14.rightCached.drop 406) (PairLightPrepared14.rightRows.drop 406) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
