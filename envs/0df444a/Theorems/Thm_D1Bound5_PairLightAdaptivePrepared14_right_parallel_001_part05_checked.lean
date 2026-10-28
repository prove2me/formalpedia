-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:12.070046+00:00
-- url     : https://prove2.me/theorems/565cd19d-a8e9-49b7-8da9-e774d9bfd56e
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 5
-- statement:
--   For prepared pair 14, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 148 through 159, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_001Part05.lean, lines 10-14, SHA-256 b75cba554377ac9fab0701d93cdab0b73ae59ded6652815f211e1f8227538b41. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part05_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 148) (PairLightPrepared14.rightRows.drop 148) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
