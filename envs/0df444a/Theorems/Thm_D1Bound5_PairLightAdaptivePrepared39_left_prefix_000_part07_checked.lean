-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:30.462993+00:00
-- url     : https://prove2.me/theorems/63122cc9-b115-43e4-913c-c16884f1ce7f
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 7
-- statement:
--   For prepared pair 39, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 84 through 95, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_000Part07.lean, lines 11-16, SHA-256 d3c20d53159b4d86a7922d9cbb65531fb19f00a829541e51f801da917638640b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_part07_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 12
      (PairLightPrepared39.leftCached.drop 84)
      (PairLightPrepared39.leftRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
