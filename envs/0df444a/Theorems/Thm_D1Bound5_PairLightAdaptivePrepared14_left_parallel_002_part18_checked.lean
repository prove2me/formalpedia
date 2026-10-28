-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part18_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part18_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:45.142312+00:00
-- url     : https://prove2.me/theorems/be92bb7f-4c49-463c-bf53-f26491ac0598
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 18
-- statement:
--   For prepared pair 14, left list, part 18, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 418 through 418, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_002Part18.lean, lines 10-14, SHA-256 23edae341b3ec6de3d45d28f3bf3c9d49424a2e0899b28b774893a93fb8bda06. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part18_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 1
      (PairLightPrepared14.leftCached.drop 418) (PairLightPrepared14.leftRows.drop 418) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
