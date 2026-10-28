-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:46.639893+00:00
-- url     : https://prove2.me/theorems/283115ef-25d7-4e95-9bf2-4e90def4ad29
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 3
-- statement:
--   For prepared pair 26, right list, part 3, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 63 through 65; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_001Part03.lean, lines 7-11, SHA-256 9114c3a5a2a29a7248ede711fb7bada250994dbdd1289c518b2ee7b9e2e9bea2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached001.drop 9) (rightRows001.drop 9) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
