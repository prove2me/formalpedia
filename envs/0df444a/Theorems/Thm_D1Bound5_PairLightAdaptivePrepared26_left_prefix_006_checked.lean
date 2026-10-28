-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_006_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:48.885418+00:00
-- url     : https://prove2.me/theorems/3e4e7fac-c0fa-418e-87fa-8a9d5351bcd5
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list
-- statement:
--   For prepared pair 26, left list, the selected-floor certificate succeeds for at most `173` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Exact original head block with every complete later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_006.lean, lines 21-111, SHA-256 25a8c837f3ad13e560b75df10d80568dad641bd117decba64fe88b3c08d649b1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 173
      leftCached006 leftRows006 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
