-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_001_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:25.488976+00:00
-- url     : https://prove2.me/theorems/c1f01481-1d85-4574-868f-6ec28930bee8
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 9
-- statement:
--   For prepared pair 14, left list, part 9, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 196 through 201, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_001Part09.lean, lines 10-14, SHA-256 edc742320415cb90e313275ad754fc2f47cf26b83d2e11ff51ccebe63bc1db58. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part09_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 6
      (PairLightPrepared14.leftCached.drop 196) (PairLightPrepared14.leftRows.drop 196) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
