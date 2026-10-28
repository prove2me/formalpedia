-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_007_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:41:24.28418+00:00
-- url     : https://prove2.me/theorems/45ff2e15-093d-45b9-b6e2-7341de7cc065
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list
-- statement:
--   For prepared pair 26, right list, the selected-floor certificate succeeds for at most `145` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Exact original head block with every complete later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_007.lean, lines 19-97, SHA-256 00392966a554249b4eac6c47d90316cf5a425f58fe06ff00aa025b116ba4afff. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_007_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 145
      rightCached007 rightRows007 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
