-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:41:57.94383+00:00
-- url     : https://prove2.me/theorems/b26524a0-cfc4-42c9-b3c4-8fe13119f5e2
-- title:
--   Selected-floor prefix certificate for prepared pair 11, left list
-- statement:
--   For prepared pair 11, left list, the selected-floor certificate succeeds for at most `138` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Heads 0 through 137; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft11_000.lean, lines 14-50, SHA-256 4610218ee4a4b3399efe5a24dfa30a415449855924e74d7660acf8d95fc395f1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 138
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
