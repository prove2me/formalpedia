-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:02.542348+00:00
-- url     : https://prove2.me/theorems/369b2be7-1412-4f2f-82ce-1b964a8ab8ea
-- title:
--   Selected-floor prefix certificate for prepared pair 29, right list, part 0
-- statement:
--   For prepared pair 29, right list, part 0, the selected-floor certificate succeeds for at most `38` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 125 through 162, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight29_001Part00.lean, lines 7-11, SHA-256 ea2f50c4700fa28a1de59d672657a7f9edf6187657576dd8945c7408d3945876. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 38
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
