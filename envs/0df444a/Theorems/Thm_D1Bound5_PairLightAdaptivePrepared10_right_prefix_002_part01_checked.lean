-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:09.870332+00:00
-- url     : https://prove2.me/theorems/701abe3a-0118-41f4-b46e-b379d6104dd0
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 1
-- statement:
--   For prepared pair 10, right list, part 1, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 168 through 183, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_002Part01.lean, lines 11-16, SHA-256 f65770c68c0618f057ef0ebc0df971f8bae0a1f2ddde8f76df890857d91dcd82. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 16
      (PairLightPrepared10.rightCached.drop 168)
      (PairLightPrepared10.rightRows.drop 168) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
