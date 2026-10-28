-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:56.295208+00:00
-- url     : https://prove2.me/theorems/3c3b818a-a75e-4807-b0ed-23c9fa040d42
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 9
-- statement:
--   For prepared pair 43, left list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 199 through 210, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_001Part09.lean, lines 8-13, SHA-256 cc2435519ca62e7087bd9754b76155d44e3f9e6e4c6c8211900d20d43bfb77a7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part09_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.leftCached.drop 199)
      (PairLightPrepared43.leftRows.drop 199) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
