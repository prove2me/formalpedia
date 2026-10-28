-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:42.949803+00:00
-- url     : https://prove2.me/theorems/d21efd7e-1791-424c-9b7b-becca48fd562
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 1
-- statement:
--   For prepared pair 43, left list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 236 through 259, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_002Part01.lean, lines 8-13, SHA-256 e76517400291c6ba9911b9d2dbd33de60985e4d79c8573a0612a202384b8528b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.leftCached.drop 236)
      (PairLightPrepared43.leftRows.drop 236) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
