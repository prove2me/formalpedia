-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:16.297558+00:00
-- url     : https://prove2.me/theorems/357d4426-e43e-4740-9340-dbc8e729a75d
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 0
-- statement:
--   For prepared pair 39, right list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 98 through 121, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_001Part00.lean, lines 11-16, SHA-256 e775c9883947005c6ec5e1ff521da44fd38bb91e6f493e7d6124f65a1a4e3c58. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 98)
      (PairLightPrepared39.rightRows.drop 98) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
