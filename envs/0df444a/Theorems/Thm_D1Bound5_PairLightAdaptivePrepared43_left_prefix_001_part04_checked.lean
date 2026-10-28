-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:39.825033+00:00
-- url     : https://prove2.me/theorems/de8f1d20-8925-4e37-bd0f-54ceb56bc441
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 4
-- statement:
--   For prepared pair 43, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 139 through 150, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_001Part04.lean, lines 8-13, SHA-256 d0edb955188b6acbc92189d876fcf5f2a6282e4e3f46fcd6b404a29c3e2893f2. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.leftCached.drop 139)
      (PairLightPrepared43.leftRows.drop 139) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
