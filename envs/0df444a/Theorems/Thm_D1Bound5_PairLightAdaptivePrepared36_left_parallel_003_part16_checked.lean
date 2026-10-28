-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part16_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part16_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:50.005505+00:00
-- url     : https://prove2.me/theorems/55dbb69a-d7d7-4b3b-91de-88f4117a4810
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 16
-- statement:
--   For prepared pair 36, left list, part 16, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 478 through 489, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part16.lean, lines 10-14, SHA-256 9e3f7d0dacab95861d6cabffe65d307ed072acf6f87a75b0a48335b6d2905646. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part16_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 478) (PairLightPrepared36.leftRows.drop 478) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
