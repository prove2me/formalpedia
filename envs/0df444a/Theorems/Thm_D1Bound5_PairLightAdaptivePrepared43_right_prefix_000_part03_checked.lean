-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:13.200833+00:00
-- url     : https://prove2.me/theorems/9f57cbf9-6b9c-44e2-9f9a-5dcaf0e8507f
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 3
-- statement:
--   For prepared pair 43, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 36 through 47, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_000Part03.lean, lines 9-14, SHA-256 ab1d1437d495c2ab59bd4962d45d75be521f54051ff5dfcb75883ef73a27ca93. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 36)
      (PairLightPrepared43.rightRows.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
