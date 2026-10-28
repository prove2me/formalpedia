-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:10.676261+00:00
-- url     : https://prove2.me/theorems/422b3555-c386-4b6f-a419-4a62f4c55954
-- title:
--   Selected-floor prefix certificate for prepared pair 29, left list, part 2
-- statement:
--   For prepared pair 29, left list, part 2, the selected-floor certificate succeeds for at most `65` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 210 through 274, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft29_001Part02.lean, lines 7-11, SHA-256 81fdf582af2fe802b98ba68ce05e9346c86cdbbde95372cc0f0f66173fac9630. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 65
      (leftCached001.drop 84) (leftRows001.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
