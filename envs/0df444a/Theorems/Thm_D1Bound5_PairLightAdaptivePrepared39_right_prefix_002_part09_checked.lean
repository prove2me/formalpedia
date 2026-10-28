-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:05.429483+00:00
-- url     : https://prove2.me/theorems/8a64ac92-7f0a-43ff-ac9d-048bb40917b9
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 9
-- statement:
--   For prepared pair 39, right list, part 9, the selected-floor certificate succeeds for at most `4` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 452 through 455, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_002Part09.lean, lines 11-16, SHA-256 90896b778f0ea3d5b0f119d1a04a97222c88523f45b0ba8c8a8bb999bf687eb5. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part09_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 4
      (PairLightPrepared39.rightCached.drop 452)
      (PairLightPrepared39.rightRows.drop 452) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
