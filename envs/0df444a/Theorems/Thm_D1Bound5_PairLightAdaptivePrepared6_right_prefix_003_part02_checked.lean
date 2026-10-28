-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:23.959507+00:00
-- url     : https://prove2.me/theorems/39e2e50d-17a4-4932-b27d-a3aa1ebfc470
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 2
-- statement:
--   For prepared pair 6, right list, part 2, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 249 through 265, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_003Part02.lean, lines 11-16, SHA-256 edd6ff1c472e0f7944564d68169a1bcb984ff30dfb1f6e930ae2baf4a94d00f6. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 17
      (PairLightPrepared6.rightCached.drop 249)
      (PairLightPrepared6.rightRows.drop 249) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
