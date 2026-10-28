-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:55.497009+00:00
-- url     : https://prove2.me/theorems/97859fd9-5ecb-44d0-83d4-ad8e6634c506
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 13
-- statement:
--   For prepared pair 14, left list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 358 through 369, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_002Part13.lean, lines 10-14, SHA-256 2809243f5ea4f0468b7e61b5b4254bc7891d0f1e338961db0e131123e5345c05. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part13_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 358) (PairLightPrepared14.leftRows.drop 358) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
