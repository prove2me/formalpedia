-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:35.605061+00:00
-- url     : https://prove2.me/theorems/66147c9c-0b67-442e-8a6d-d816d9703ae1
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 9
-- statement:
--   For prepared pair 39, left list, part 9, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 449 through 457, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_002Part09.lean, lines 11-16, SHA-256 28d985200d5ac35e3d821a05167b42931cee6bef8fb78e025f1d7a01a395c088. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_part09_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 9
      (PairLightPrepared39.leftCached.drop 449)
      (PairLightPrepared39.leftRows.drop 449) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
