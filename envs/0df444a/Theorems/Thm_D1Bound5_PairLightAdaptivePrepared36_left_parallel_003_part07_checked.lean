-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:57.668575+00:00
-- url     : https://prove2.me/theorems/1e1848e3-e995-4dce-b1d1-eb3c16ee69c1
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 7
-- statement:
--   For prepared pair 36, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 370 through 381, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part07.lean, lines 10-14, SHA-256 c3ffc903140dd9cb666c92d7b23427af19a0ed8aa76d53b9124580d4eb58617d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part07_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 370) (PairLightPrepared36.leftRows.drop 370) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
