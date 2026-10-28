-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_001_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:44.436191+00:00
-- url     : https://prove2.me/theorems/d286af54-29bb-4516-beca-2bc025ae16a4
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 7
-- statement:
--   For prepared pair 36, left list, part 7, the selected-floor certificate succeeds for at most `7` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 160 through 166, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_001Part07.lean, lines 10-14, SHA-256 3174d765c53cd2c6e2947230fe32c8c57d9e2e93e8ae9ad18d39e07123b2e93f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_001_part07_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 7
      (PairLightPrepared36.leftCached.drop 160) (PairLightPrepared36.leftRows.drop 160) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
