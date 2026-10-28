-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:53.491048+00:00
-- url     : https://prove2.me/theorems/afa85275-68a3-4100-b8cc-6d34da4c7c7b
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list
-- statement:
--   For prepared pair 36, left list, the selected-floor certificate succeeds for at most `91` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft36_001.lean, lines 16-63, SHA-256 3a995830abefe4e42321ca4bc4027e15d19a9a5fc6a30c4a34348e7f8d97498b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 91
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
