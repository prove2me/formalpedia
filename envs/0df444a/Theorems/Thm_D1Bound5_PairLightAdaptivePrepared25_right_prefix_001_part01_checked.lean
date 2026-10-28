-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:51.941184+00:00
-- url     : https://prove2.me/theorems/534b02b2-3eda-42e3-a382-921a36713357
-- title:
--   Selected-floor prefix certificate for prepared pair 25, right list, part 1
-- statement:
--   For prepared pair 25, right list, part 1, the selected-floor certificate succeeds for at most `46` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 163 through 208, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight25_001Part01.lean, lines 7-11, SHA-256 5215422df3d2d1013c9e9fc47d8dffe648f447af86127dab0a11bfdc035feccd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 46
      (rightCached001.drop 38) (rightRows001.drop 38) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
