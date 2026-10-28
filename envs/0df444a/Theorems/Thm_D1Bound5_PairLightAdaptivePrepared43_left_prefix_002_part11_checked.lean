-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part11_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:08.653697+00:00
-- url     : https://prove2.me/theorems/8e78bc40-69c9-4f39-98b7-16b18190e784
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 11
-- statement:
--   For prepared pair 43, left list, part 11, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 476 through 481, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_002Part11.lean, lines 8-13, SHA-256 759e64c1185b485596e13dfd4139af05be3881ea9655b3b9f2cb99c0ae7639aa. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part11_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 6
      (PairLightPrepared43.leftCached.drop 476)
      (PairLightPrepared43.leftRows.drop 476) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
