-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:04.674528+00:00
-- url     : https://prove2.me/theorems/0eab9b9d-a7a0-42ff-bdc6-d35da6a1d31c
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 7
-- statement:
--   For prepared pair 39, right list, part 7, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 404 through 427, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_002Part07.lean, lines 11-16, SHA-256 7ec7d9fea00c90f10e8434d3874c1fc89e509f0f075ae46a84334c89d980915e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part07_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 404)
      (PairLightPrepared39.rightRows.drop 404) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
