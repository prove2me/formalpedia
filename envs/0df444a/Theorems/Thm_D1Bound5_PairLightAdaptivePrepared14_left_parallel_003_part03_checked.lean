-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_003_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_003_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:36.822005+00:00
-- url     : https://prove2.me/theorems/f50c6410-b818-47af-ae12-c46d5e54fc8f
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 3
-- statement:
--   For prepared pair 14, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 455 through 466, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_003Part03.lean, lines 10-14, SHA-256 4311a4a6934b16b94a37ad54d66560ddb02c596b568ca53bd6fdb75291e41a4c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_003_part03_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 455) (PairLightPrepared14.leftRows.drop 455) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
