-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_005_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_005_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:37:24.634992+00:00
-- url     : https://prove2.me/theorems/2f7950a8-aff4-4e15-8734-91464dc3d3e5
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 0
-- statement:
--   For prepared pair 6, right list, part 0, the selected-floor certificate succeeds for at most `38` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 476 through 513, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_005Part00.lean, lines 11-16, SHA-256 a393dc8fd0b4928d62c53c4a79b4a7c37629e972fd433c842f138cbd8e36cf01. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_005_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 38
      (PairLightPrepared6.rightCached.drop 476)
      (PairLightPrepared6.rightRows.drop 476) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
