-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:48.321188+00:00
-- url     : https://prove2.me/theorems/651fb516-6d83-4899-b335-10f32b552f4b
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 5
-- statement:
--   For prepared pair 43, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 60 through 71, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_000Part05.lean, lines 9-14, SHA-256 0359f61b26cd2302f35eb53b23d8d9b14566540b80f2f92b4dbeb15c498fdbac. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 60)
      (PairLightPrepared43.rightRows.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
