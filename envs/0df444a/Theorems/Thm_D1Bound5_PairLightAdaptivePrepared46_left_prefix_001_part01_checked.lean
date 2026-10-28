-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:47.237576+00:00
-- url     : https://prove2.me/theorems/6f160ad9-ce9e-4492-98e8-07d5f9d7db93
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list, part 1
-- statement:
--   For prepared pair 46, left list, part 1, the selected-floor certificate succeeds for at most `42` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 171 through 212, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_001Part01.lean, lines 7-11, SHA-256 ba1aeb42b1d3018bcbfaada8ac4db9b56970023423f5d08ba7d03b0b9fcbac77. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 42
      (leftCached001.drop 34) (leftRows001.drop 34) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
