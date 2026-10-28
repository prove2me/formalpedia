-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_005_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:49:09.514436+00:00
-- url     : https://prove2.me/theorems/2a99fbd1-b895-40ee-b717-501cee5fe91a
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list
-- statement:
--   For prepared pair 26, left list, the selected-floor certificate succeeds for at most `107` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Exact original head block with every complete later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_005.lean, lines 15-69, SHA-256 ab21d8ad901a541f473909587a176f39048db059cee3bb88c07cb67974a94542. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 107
      leftCached005 leftRows005 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
