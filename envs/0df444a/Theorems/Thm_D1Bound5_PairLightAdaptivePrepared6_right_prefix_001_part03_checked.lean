-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:55.090987+00:00
-- url     : https://prove2.me/theorems/5de124b4-4173-4a50-a26e-1719ca84570e
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 3
-- statement:
--   For prepared pair 6, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 99 through 110, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_001Part03.lean, lines 11-16, SHA-256 5260d41dc5c44c1a8dd6c84fed0b074de5d640b82e4c7ed590d4ac37591fa3f8. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 12
      (PairLightPrepared6.rightCached.drop 99)
      (PairLightPrepared6.rightRows.drop 99) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
