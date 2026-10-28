-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:43.29045+00:00
-- url     : https://prove2.me/theorems/2d02ff82-36eb-49e9-bb7b-0925e59df3bb
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list
-- statement:
--   For prepared pair 1, left list, the selected-floor certificate succeeds for at most `223` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Heads 137 through 359; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_001.lean, lines 12-36, SHA-256 50c3928b565d571161184b715f8d55de9304d8a0a7044c0ac031268c6a2a5cf2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 223
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
