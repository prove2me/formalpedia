-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part15_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:23.471967+00:00
-- url     : https://prove2.me/theorems/769d3423-e77e-4c94-ac84-d08359e7d43b
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 15
-- statement:
--   For prepared pair 23, left list, part 15, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 392 through 403, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_002Part15.lean, lines 10-14, SHA-256 3dd5d0a848fc29b7502234b46ed1537f9f78d41e71ffb03c0e1b40efb2875541. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part15_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 392) (PairLightPrepared23.leftRows.drop 392) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
