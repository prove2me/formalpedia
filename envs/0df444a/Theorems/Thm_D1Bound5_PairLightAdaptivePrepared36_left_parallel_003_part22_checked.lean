-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part22_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:10.845421+00:00
-- url     : https://prove2.me/theorems/e6d2b614-4616-4eba-a64d-c486953f09eb
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 22
-- statement:
--   For prepared pair 36, left list, part 22, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 550 through 560, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part22.lean, lines 10-14, SHA-256 121eb44a50804255140d96c87ac061f05660e9e543ceffdfb3b7ba9fee176292. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part22_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 11
      (PairLightPrepared36.leftCached.drop 550) (PairLightPrepared36.leftRows.drop 550) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
