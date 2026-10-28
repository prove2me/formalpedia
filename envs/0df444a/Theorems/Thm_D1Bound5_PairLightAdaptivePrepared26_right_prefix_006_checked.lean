-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:39.318351+00:00
-- url     : https://prove2.me/theorems/9f0a3f5c-c7af-4cb9-8573-efbb9f53566d
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list
-- statement:
--   For prepared pair 26, right list, the selected-floor certificate succeeds for at most `173` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Exact original head block with every complete later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_006.lean, lines 21-111, SHA-256 d03001f0816874650894407d2e8a4cb485e47bc2d6d328ab09cf5c344a077ea6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 173
      rightCached006 rightRows006 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
