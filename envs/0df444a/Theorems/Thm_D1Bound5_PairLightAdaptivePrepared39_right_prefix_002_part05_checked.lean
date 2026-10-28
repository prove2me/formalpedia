-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:53:14.421215+00:00
-- url     : https://prove2.me/theorems/6506093e-36b8-44b9-9faa-74b9814219c1
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 5
-- statement:
--   For prepared pair 39, right list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 356 through 379, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_002Part05.lean, lines 11-16, SHA-256 df9d90a26672d04fc0e403562cf7cdc6c457da4b11854717f6c19137b4cc2bf7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 356)
      (PairLightPrepared39.rightRows.drop 356) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
