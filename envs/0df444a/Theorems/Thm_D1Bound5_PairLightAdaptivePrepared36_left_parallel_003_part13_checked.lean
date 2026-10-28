-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:06.511852+00:00
-- url     : https://prove2.me/theorems/7097c8a3-ac3f-4a8a-9fb9-17d3c9de4e6c
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 13
-- statement:
--   For prepared pair 36, left list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 442 through 453, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part13.lean, lines 10-14, SHA-256 578c9c8d421f34ee2763b89efa6422dfc8f5f85f627c6cab4b3daf35451ec7e3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part13_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 442) (PairLightPrepared36.leftRows.drop 442) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
