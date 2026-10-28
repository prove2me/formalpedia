-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:04.049992+00:00
-- url     : https://prove2.me/theorems/004e685c-93a6-43c6-b5b5-291d318a1f19
-- title:
--   Selected-floor prefix certificate for prepared pair 25, left list, part 1
-- statement:
--   For prepared pair 25, left list, part 1, the selected-floor certificate succeeds for at most `46` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 164 through 209, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft25_001Part01.lean, lines 7-11, SHA-256 c3e792f0e3077118de17bb2edce9bb7f8232610059332bc9af9e113767283cc8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 46
      (leftCached001.drop 38) (leftRows001.drop 38) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
