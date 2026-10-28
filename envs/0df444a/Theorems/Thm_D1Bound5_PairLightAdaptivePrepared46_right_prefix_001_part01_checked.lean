-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:21.984925+00:00
-- url     : https://prove2.me/theorems/b1a2e15b-4e13-4e30-bd80-4620a08d608c
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list, part 1
-- statement:
--   For prepared pair 46, right list, part 1, the selected-floor certificate succeeds for at most `42` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 172 through 213, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_001Part01.lean, lines 7-11, SHA-256 83b8b10226322d325cb2e6b68045490a70ea2519d5ac6ec7879e017413f85912. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 42
      (rightCached001.drop 34) (rightRows001.drop 34) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
