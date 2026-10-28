-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part19_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part19_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:32.562024+00:00
-- url     : https://prove2.me/theorems/0395fc6e-6cc1-4d80-8ad6-bf30d7a2b865
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 19
-- statement:
--   For prepared pair 15, left list, part 19, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 442 through 453, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_002Part19.lean, lines 10-14, SHA-256 35875db9c3964f437b7024376c4bf625b0e1d26f3808291c850022548a5a46b7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part19_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 442) (PairLightPrepared15.leftRows.drop 442) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
