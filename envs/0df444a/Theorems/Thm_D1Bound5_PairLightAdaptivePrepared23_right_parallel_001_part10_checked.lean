-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_001_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:02.256824+00:00
-- url     : https://prove2.me/theorems/de2a7286-04e2-413d-a804-8b76a531220b
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 10
-- statement:
--   For prepared pair 23, right list, part 10, the selected-floor certificate succeeds for at most `2` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 212 through 213, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_001Part10.lean, lines 10-14, SHA-256 407680b0558bbb429bacc9653f5f7f30a365f1f1d36dc324ab5dd0447cfc8d34. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 2
      (PairLightPrepared23.rightCached.drop 212) (PairLightPrepared23.rightRows.drop 212) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
