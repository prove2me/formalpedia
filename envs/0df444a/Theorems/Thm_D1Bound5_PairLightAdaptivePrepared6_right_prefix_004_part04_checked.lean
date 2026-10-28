-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:45.989981+00:00
-- url     : https://prove2.me/theorems/6a3f84aa-814f-4558-8253-507a461626c8
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 4
-- statement:
--   For prepared pair 6, right list, part 4, the selected-floor certificate succeeds for at most `28` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 411 through 438, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_004Part04.lean, lines 11-16, SHA-256 e67488f8366bfbcdb308926d594ad2be4e391fe3a6b0b581802de3acfe847282. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 28
      (PairLightPrepared6.rightCached.drop 411)
      (PairLightPrepared6.rightRows.drop 411) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
