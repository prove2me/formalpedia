-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part11_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:01.75998+00:00
-- url     : https://prove2.me/theorems/28376529-e93c-4ef0-b4ca-1f6bd7ef7664
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 11
-- statement:
--   For prepared pair 26, left list, part 11, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 33 through 35 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_000Part11.lean, lines 7-11, SHA-256 8102ba96b395de4509dd8fa00b2b21b3de7cbc365986ada19df8f2fe0e23150d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part11_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached000.drop 33) (leftRows000.drop 33) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
