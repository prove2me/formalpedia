-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:40.820047+00:00
-- url     : https://prove2.me/theorems/599c4621-76a8-4ec0-bfa1-5fee51813256
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 4
-- statement:
--   For prepared pair 26, left list, part 4, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 125 through 127; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part04.lean, lines 7-11, SHA-256 fa47fe2c9f7573863729aa131ecee3ea981351a9e27b8a0eb3801ed6e6c3e5e1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 12) (leftRows002.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
