-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_001_part11_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:11.841126+00:00
-- url     : https://prove2.me/theorems/13c7954c-d181-48ba-a9fa-1811ea6c13c6
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 11
-- statement:
--   For prepared pair 26, left list, part 11, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 87 through 89; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_001Part11.lean, lines 7-11, SHA-256 0c9ef9a94006d47e0c7d66063673bb6de25ea34ca930da6b1e11f11ca0371779. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part11_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached001.drop 33) (leftRows001.drop 33) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
