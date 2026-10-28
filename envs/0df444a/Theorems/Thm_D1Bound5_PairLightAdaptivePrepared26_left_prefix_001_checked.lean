-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:17.805899+00:00
-- url     : https://prove2.me/theorems/9b5dd782-6aa7-4e44-828f-db27f7b5b6ff
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list
-- statement:
--   For prepared pair 26, left list, the selected-floor certificate succeeds for at most `59` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Exact original head block; every head retains its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_001.lean, lines 26-146, SHA-256 2a81d1f7920a7b0ea4c2343a7ccd0074ea8a6a13c7efe2e00a10b860be17717d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 59
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
