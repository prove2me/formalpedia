-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:56.73482+00:00
-- url     : https://prove2.me/theorems/2e72987d-fc73-473a-bff9-1aa1f0aa490e
-- title:
--   Selected-floor prefix certificate for prepared pair 35, right list, part 3
-- statement:
--   For prepared pair 35, right list, part 3, the selected-floor certificate succeeds for at most `39` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 92 through 130; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight35_000Part03.lean, lines 7-11, SHA-256 c23a744e19653beb59560128cadd6bdcb4b01f40d79542c6d7fd205a2f958694. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 39
      (rightCached000.drop 92) (rightRows000.drop 92) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
