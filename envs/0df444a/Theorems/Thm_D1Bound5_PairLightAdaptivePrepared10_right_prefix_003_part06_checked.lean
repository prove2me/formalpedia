-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:05.549003+00:00
-- url     : https://prove2.me/theorems/ad9d28d6-1b3b-4fe8-a916-27e4f2334372
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 6
-- statement:
--   For prepared pair 10, right list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 402 through 404, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_003Part06.lean, lines 11-16, SHA-256 dbf44cb62dfd60f245ac0afd6f0fb55535c3bdeceabe2111baa5509c2118e70c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 3
      (PairLightPrepared10.rightCached.drop 402)
      (PairLightPrepared10.rightRows.drop 402) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
