-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:37.982341+00:00
-- url     : https://prove2.me/theorems/610ac81e-c899-4db4-929f-dfa5485738e2
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list
-- statement:
--   For prepared pair 40, left list, the selected-floor certificate succeeds for at most `223` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Heads 137 through 359; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_001.lean, lines 11-29, SHA-256 9d2db6affe8ba52c4b33787835f30368f4c5b1f553be145216585ec6fec528e4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 223
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
