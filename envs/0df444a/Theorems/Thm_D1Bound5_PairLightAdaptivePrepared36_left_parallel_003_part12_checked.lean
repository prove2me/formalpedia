-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:41.448672+00:00
-- url     : https://prove2.me/theorems/907662a9-4052-43b2-8e14-004aa9c45172
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 12
-- statement:
--   For prepared pair 36, left list, part 12, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 430 through 441, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part12.lean, lines 10-14, SHA-256 2b1c159fdb5ab8f6662ef043797c2258c14ee1206981d4874db97868f4e5a856. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part12_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 430) (PairLightPrepared36.leftRows.drop 430) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
