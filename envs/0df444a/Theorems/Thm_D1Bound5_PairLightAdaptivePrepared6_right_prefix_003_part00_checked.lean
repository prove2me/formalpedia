-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:10.94768+00:00
-- url     : https://prove2.me/theorems/0847eb77-5ffa-4746-8731-7b99707a6631
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 0
-- statement:
--   For prepared pair 6, right list, part 0, the selected-floor certificate succeeds for at most `15` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 218 through 232, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_003Part00.lean, lines 11-16, SHA-256 159b271ba08faec1dae14c77a0712a11f47e9e5f58d5bb6770552cb74acc46e1. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 15
      (PairLightPrepared6.rightCached.drop 218)
      (PairLightPrepared6.rightRows.drop 218) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
