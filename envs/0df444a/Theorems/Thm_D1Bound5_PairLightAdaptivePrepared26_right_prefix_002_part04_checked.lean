-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:17.681077+00:00
-- url     : https://prove2.me/theorems/c69df7a3-7bff-409f-b47b-ed81ad2a98db
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 4
-- statement:
--   For prepared pair 26, right list, part 4, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 125 through 127; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_002Part04.lean, lines 7-11, SHA-256 70074cb04bae537076b1b76392806311531836cfc787ab5ce76b98ce7329a022. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached002.drop 12) (rightRows002.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
