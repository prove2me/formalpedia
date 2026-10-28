-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:34.518374+00:00
-- url     : https://prove2.me/theorems/442bdadc-ac83-483e-9589-e4b3ba36ff71
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 10
-- statement:
--   For prepared pair 26, right list, part 10, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 84 through 86; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_001Part10.lean, lines 7-11, SHA-256 3db54685697fbb402e15fc244d4a5aed1b3c88d81ba40c811599c50b6ae91ed3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached001.drop 30) (rightRows001.drop 30) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
