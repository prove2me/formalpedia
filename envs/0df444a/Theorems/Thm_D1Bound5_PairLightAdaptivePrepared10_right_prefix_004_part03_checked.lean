-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_004_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_004_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:59.904215+00:00
-- url     : https://prove2.me/theorems/33e520ae-c82a-41a7-83cc-74c57a81f7c4
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 3
-- statement:
--   For prepared pair 10, right list, part 3, the selected-floor certificate succeeds for at most `46` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 550 through 595, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_004Part03.lean, lines 11-16, SHA-256 496c45bde549d9aa0ed45f792c47ea8f76e7e9e3f35dea7ad4a1ed78c01f70c5. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_004_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 46
      (PairLightPrepared10.rightCached.drop 550)
      (PairLightPrepared10.rightRows.drop 550) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
