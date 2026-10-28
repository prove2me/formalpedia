-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:50.064986+00:00
-- url     : https://prove2.me/theorems/74978301-1a02-4d2f-beb2-68853b7e5e62
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 14
-- statement:
--   For prepared pair 14, right list, part 14, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 370 through 381, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_002Part14.lean, lines 10-14, SHA-256 dba27bf1124df0bee24151187891ae1f0bd091d4bc4180c9e2aff414261abd55. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part14_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 370) (PairLightPrepared14.rightRows.drop 370) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
