-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:03.343248+00:00
-- url     : https://prove2.me/theorems/8023d804-de2d-46f5-84b2-544f70e57d7f
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 5
-- statement:
--   For prepared pair 23, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 152 through 163, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_001Part05.lean, lines 10-14, SHA-256 61bc63ca3a4d62e0d759a6314a2c4754436f6b7a8b6e9cd92a64996b2683b241. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 152) (PairLightPrepared23.rightRows.drop 152) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
