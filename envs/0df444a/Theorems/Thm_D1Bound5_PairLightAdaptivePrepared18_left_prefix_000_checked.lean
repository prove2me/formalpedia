-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:32.692468+00:00
-- url     : https://prove2.me/theorems/9f989c16-8878-4bb7-89d3-e051375263c6
-- title:
--   Selected-floor prefix certificate for prepared pair 18, left list
-- statement:
--   For prepared pair 18, left list, the selected-floor certificate succeeds for at most `262` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared18.sieve`. Heads 0 through 261; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft18_000.lean, lines 12-36, SHA-256 ca2eac3a3a324a8e4b012c176459d06d974a9ce23906415da89e2d273d9ad6a8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 262
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared18
end
