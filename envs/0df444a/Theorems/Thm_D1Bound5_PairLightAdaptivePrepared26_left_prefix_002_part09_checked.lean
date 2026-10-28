-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:59.003103+00:00
-- url     : https://prove2.me/theorems/9e2e8157-4782-4a88-b43b-6fb89c758ba4
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 9
-- statement:
--   For prepared pair 26, left list, part 9, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 140 through 142; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part09.lean, lines 7-11, SHA-256 214e971adb496012f629e51a76ec2cb88f01d36d86f0ca76f4d07d49d6bfa1b0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part09_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 27) (leftRows002.drop 27) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
