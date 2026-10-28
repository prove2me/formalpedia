-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:03.635735+00:00
-- url     : https://prove2.me/theorems/a52fbbeb-348f-4e7f-9b45-e0f460b8358f
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 6
-- statement:
--   For prepared pair 36, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 358 through 369, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part06.lean, lines 10-14, SHA-256 6e20ddf8fc693cbb23d017f57905a49d0e0ec02a08351ad3b5c5667f46e78464. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part06_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 358) (PairLightPrepared36.leftRows.drop 358) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
