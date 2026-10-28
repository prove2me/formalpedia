-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:20:08.053075+00:00
-- url     : https://prove2.me/theorems/8ec740ca-1bcd-4904-82e0-0bd3c9a80723
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 2
-- statement:
--   For prepared pair 43, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 116 through 127, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_001Part02.lean, lines 9-14, SHA-256 a21c308e47db351247e69bb3fbde2912e9027db9e939ce3e5fe3375d809c8d96. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 116)
      (PairLightPrepared43.rightRows.drop 116) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
