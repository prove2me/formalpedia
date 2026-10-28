-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:26.773861+00:00
-- url     : https://prove2.me/theorems/2bda18f4-0e98-4c0e-8c70-a0d33cbdff3e
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 1
-- statement:
--   For prepared pair 26, right list, part 1, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 57 through 59; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_001Part01.lean, lines 7-11, SHA-256 194950b76ef78432c44c2bf3593e9825f8fd2e91d012e0133b7a250146b0a90e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached001.drop 3) (rightRows001.drop 3) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
