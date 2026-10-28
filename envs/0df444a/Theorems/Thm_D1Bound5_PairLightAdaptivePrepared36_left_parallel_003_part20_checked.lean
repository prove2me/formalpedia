-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part20_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part20_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:55:48.74299+00:00
-- url     : https://prove2.me/theorems/3a006900-9d31-42ec-83db-e6836e8bf6d9
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 20
-- statement:
--   For prepared pair 36, left list, part 20, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 526 through 537, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part20.lean, lines 10-14, SHA-256 06296af853556f6141dea9c94de52db767fe719e6d94f8f0c25af51e18f66a46. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part20_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 526) (PairLightPrepared36.leftRows.drop 526) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
