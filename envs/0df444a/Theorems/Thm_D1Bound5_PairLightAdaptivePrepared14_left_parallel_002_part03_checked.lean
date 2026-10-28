-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:45.875508+00:00
-- url     : https://prove2.me/theorems/e374b06c-5bbb-40b9-aace-25da0c2d47c3
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 3
-- statement:
--   For prepared pair 14, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 238 through 249, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_002Part03.lean, lines 10-14, SHA-256 246640b0c2fbbe985872c7693bc218e98a4bc2155e1a5b70235df5f7d485b002. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part03_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 238) (PairLightPrepared14.leftRows.drop 238) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
