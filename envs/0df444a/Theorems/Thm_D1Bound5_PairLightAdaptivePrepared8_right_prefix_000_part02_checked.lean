-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:43.975611+00:00
-- url     : https://prove2.me/theorems/3533d2b7-e157-4055-93f9-a8ba4c91290e
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 2
-- statement:
--   For prepared pair 8, right list, part 2, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 18 through 27, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_000Part02.lean, lines 11-16, SHA-256 67940ae04878916884fccd43b50d53fd125af0ffc4d890dabcb12e2d112c851b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 10
      (PairLightPrepared8.rightCached.drop 18)
      (PairLightPrepared8.rightRows.drop 18) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
