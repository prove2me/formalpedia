-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_005_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_005_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:14.52402+00:00
-- url     : https://prove2.me/theorems/42029482-a810-4675-ad9e-3f18f54f9be9
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 2
-- statement:
--   For prepared pair 6, right list, part 2, the selected-floor certificate succeeds for at most `75` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 563 through 637, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_005Part02.lean, lines 11-16, SHA-256 5e6934ebbcc0cb7f2eaeea111a3ae79ae55eb6dc8094700f8e5360aad08a0b08. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_005_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 75
      (PairLightPrepared6.rightCached.drop 563)
      (PairLightPrepared6.rightRows.drop 563) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
