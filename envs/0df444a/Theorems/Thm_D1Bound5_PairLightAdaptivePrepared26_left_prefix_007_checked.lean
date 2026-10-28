-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:40:30.449818+00:00
-- url     : https://prove2.me/theorems/72436e32-b4d3-4117-96fc-1773d417c434
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list
-- statement:
--   For prepared pair 26, left list, the selected-floor certificate succeeds for at most `145` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Exact original head block with every complete later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_007.lean, lines 19-97, SHA-256 eb2146bf96aa8e27999dd5d2eb7007be8a56e0c33505d72f1ae60fbe4ce41820. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 145
      leftCached007 leftRows007 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
