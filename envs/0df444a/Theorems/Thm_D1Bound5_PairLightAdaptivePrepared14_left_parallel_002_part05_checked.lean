-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:55.236037+00:00
-- url     : https://prove2.me/theorems/42613145-e7c9-40c4-9f5f-5142a10f8d01
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 5
-- statement:
--   For prepared pair 14, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 262 through 273, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_002Part05.lean, lines 10-14, SHA-256 760d1718c3096dbcaea6ec1f7822fac36624ebf7a8d8f2c1a0feba6ea8fafa5f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part05_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 262) (PairLightPrepared14.leftRows.drop 262) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
