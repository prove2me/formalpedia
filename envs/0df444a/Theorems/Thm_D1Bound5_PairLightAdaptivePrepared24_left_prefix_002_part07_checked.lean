-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:11.770858+00:00
-- url     : https://prove2.me/theorems/5260f753-d4f4-4d1a-a9e7-c55930c2e68b
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 7
-- statement:
--   For prepared pair 24, left list, part 7, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 416 through 439, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_002Part07.lean, lines 11-16, SHA-256 fdeed2c9d38e2c0e95eeebc019252e325c09b95fb55bb55fe8d0aa60c172ba63. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 416)
      (PairLightPrepared24.leftRows.drop 416) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
