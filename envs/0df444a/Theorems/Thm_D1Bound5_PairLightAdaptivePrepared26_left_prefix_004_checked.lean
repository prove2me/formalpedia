-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_004_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_004_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:40:08.269339+00:00
-- url     : https://prove2.me/theorems/736eafd3-372a-4dd7-a934-a9c92a1a59dc
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list
-- statement:
--   For prepared pair 26, left list, the selected-floor certificate succeeds for at most `85` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Exact original head block with every complete later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_004.lean, lines 14-62, SHA-256 4f44fca524e580b8062ff235789119b3c273be0451a33848413a9fe459d28013. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_004_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 85
      leftCached004 leftRows004 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
