-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:53:21.241643+00:00
-- url     : https://prove2.me/theorems/d2564ac6-8284-479d-ade5-403bd058c3c9
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 0
-- statement:
--   For prepared pair 36, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 286 through 297, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part00.lean, lines 10-14, SHA-256 e208ffe7e560cb8769cf56c84b8b076712a38a8137cb082ff42410da5bbf9621. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 286) (PairLightPrepared36.leftRows.drop 286) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
