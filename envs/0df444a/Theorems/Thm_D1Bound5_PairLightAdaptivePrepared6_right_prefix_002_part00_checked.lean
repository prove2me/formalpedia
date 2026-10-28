-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:47.752133+00:00
-- url     : https://prove2.me/theorems/745d4fbf-68d2-43d8-8d9f-38e2f80c0b58
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 0
-- statement:
--   For prepared pair 6, right list, part 0, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 135 through 147, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_002Part00.lean, lines 11-16, SHA-256 416928458bad190ad87c30ff8c74100ba6527709d2e8e3f64065a3f73d6d2fd4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 13
      (PairLightPrepared6.rightCached.drop 135)
      (PairLightPrepared6.rightRows.drop 135) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
