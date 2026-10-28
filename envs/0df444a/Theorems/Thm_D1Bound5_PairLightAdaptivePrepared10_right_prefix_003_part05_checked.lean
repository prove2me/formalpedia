-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:12.9334+00:00
-- url     : https://prove2.me/theorems/9e34feb0-5ecc-4f72-98ba-23a7702b89fb
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 5
-- statement:
--   For prepared pair 10, right list, part 5, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 371 through 401, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_003Part05.lean, lines 11-16, SHA-256 00370c6b5a59dcea11dd2faeb62dd2daf107f7d4ee27d81f04ba6f14084729fe. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 31
      (PairLightPrepared10.rightCached.drop 371)
      (PairLightPrepared10.rightRows.drop 371) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
