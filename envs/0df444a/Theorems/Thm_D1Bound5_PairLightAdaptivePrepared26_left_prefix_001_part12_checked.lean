-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_001_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:34.944988+00:00
-- url     : https://prove2.me/theorems/0d9bc811-8e19-4f27-a83d-8a80582e8d2c
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 12
-- statement:
--   For prepared pair 26, left list, part 12, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 90 through 92; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_001Part12.lean, lines 7-11, SHA-256 6dd067f7ef8ecfb48f1152419467372121f3d5f642869a1d1656a7d8f7e2db10. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part12_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached001.drop 36) (leftRows001.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
