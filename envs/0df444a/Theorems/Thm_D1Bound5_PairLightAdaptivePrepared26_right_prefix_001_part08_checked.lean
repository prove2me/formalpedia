-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:35.00965+00:00
-- url     : https://prove2.me/theorems/d4480029-f934-447d-950c-813054e569b2
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 8
-- statement:
--   For prepared pair 26, right list, part 8, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 78 through 80; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_001Part08.lean, lines 7-11, SHA-256 9d6246fa07227712379199aa410068e002cff91f427e53d065b76859d19b116d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached001.drop 24) (rightRows001.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
