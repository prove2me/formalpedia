-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:06.841781+00:00
-- url     : https://prove2.me/theorems/e88d108e-d5b2-4180-9ea3-95d90c1e8cec
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 0
-- statement:
--   For prepared pair 26, right list, part 0, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 54 through 56; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_001Part00.lean, lines 7-11, SHA-256 2797f4953d5da1bdfa0f93fcbf0a8fa7c1eef6d127d9700e992f08c7f00480a2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
