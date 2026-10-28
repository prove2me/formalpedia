-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_003_part15_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:04.021006+00:00
-- url     : https://prove2.me/theorems/f1241660-15ef-45d2-9fe9-d473449dd92d
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 15
-- statement:
--   For prepared pair 21, left list, part 15, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 515 through 523, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_003Part15.lean, lines 10-14, SHA-256 4bdd928df8b630ffdc3e848d1f7ba0aedade38411e186a09e8eeea58b35ae73c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part15_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 9
      (PairLightPrepared21.leftCached.drop 515) (PairLightPrepared21.leftRows.drop 515) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
