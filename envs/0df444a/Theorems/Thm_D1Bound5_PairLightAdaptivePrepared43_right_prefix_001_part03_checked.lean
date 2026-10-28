-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:11.737675+00:00
-- url     : https://prove2.me/theorems/05175342-ea6a-46c7-adeb-f612c5ddf2e0
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 3
-- statement:
--   For prepared pair 43, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 128 through 139, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_001Part03.lean, lines 9-14, SHA-256 c74f6d4571aaf63e4d7d7cf93d1d1e65a9802d31221c87367a5198f00f0bdd4f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 128)
      (PairLightPrepared43.rightRows.drop 128) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
