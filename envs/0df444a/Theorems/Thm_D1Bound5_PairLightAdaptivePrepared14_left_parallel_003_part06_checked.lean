-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:51.797993+00:00
-- url     : https://prove2.me/theorems/0d2f7ea7-b61e-4f1c-90fd-aebf4018d0a7
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 6
-- statement:
--   For prepared pair 14, left list, part 6, the selected-floor certificate succeeds for at most `4` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 491 through 494, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_003Part06.lean, lines 10-14, SHA-256 6a903fa44c15370151e566725519d6563456b366e5ce3e7d3c2a6f7f4da1c17b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_003_part06_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 4
      (PairLightPrepared14.leftCached.drop 491) (PairLightPrepared14.leftRows.drop 491) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
