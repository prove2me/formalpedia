-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_006_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_006_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:00.440932+00:00
-- url     : https://prove2.me/theorems/7c318551-916c-42d2-855e-729006873068
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 0
-- statement:
--   For prepared pair 8, right list, part 0, the selected-floor certificate succeeds for at most `36` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 524 through 559, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_006Part00.lean, lines 11-16, SHA-256 df32d246d1e76ebd7f4bcbf98527ca826e560c64dd0c88ba5dea45e9e61a2109. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_006_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 36
      (PairLightPrepared8.rightCached.drop 524)
      (PairLightPrepared8.rightRows.drop 524) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
