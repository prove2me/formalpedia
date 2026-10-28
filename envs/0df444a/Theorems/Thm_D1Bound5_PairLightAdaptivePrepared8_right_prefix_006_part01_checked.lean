-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_006_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_006_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:56.503735+00:00
-- url     : https://prove2.me/theorems/6eaafb5f-eb5c-4a76-bbb9-d8f5026d214a
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 1
-- statement:
--   For prepared pair 8, right list, part 1, the selected-floor certificate succeeds for at most `44` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 560 through 603, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_006Part01.lean, lines 11-16, SHA-256 1c0de3a97b8c8331de3544761f9b6c446888e54677a8007be94179168960cc1f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_006_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 44
      (PairLightPrepared8.rightCached.drop 560)
      (PairLightPrepared8.rightRows.drop 560) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
