-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:25.819756+00:00
-- url     : https://prove2.me/theorems/261c8a34-40e9-4669-9fbe-6a940f16f305
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 2
-- statement:
--   For prepared pair 26, right list, part 2, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 119 through 121; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_002Part02.lean, lines 7-11, SHA-256 e2adc862352c8f8a34106d529ceed07d61e6b1d6a5d52fa04cb5da91bea8a398. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached002.drop 6) (rightRows002.drop 6) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
