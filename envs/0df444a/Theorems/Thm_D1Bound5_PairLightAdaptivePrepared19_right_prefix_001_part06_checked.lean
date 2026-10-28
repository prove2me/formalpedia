-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:36.329761+00:00
-- url     : https://prove2.me/theorems/c06ab6dc-20fd-450a-ae88-56509381458f
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 6
-- statement:
--   For prepared pair 19, right list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 245 through 247, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_001Part06.lean, lines 11-16, SHA-256 a9c01861100bcb62028e53035e215aab0c4b6111b7d29c1b0dbc32afbb78b40c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 3
      (PairLightPrepared19.rightCached.drop 245)
      (PairLightPrepared19.rightRows.drop 245) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
