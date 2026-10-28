-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:17.086076+00:00
-- url     : https://prove2.me/theorems/4165e11e-d770-4c92-9d13-a378074acd0c
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list
-- statement:
--   For prepared pair 15, left list, the selected-floor certificate succeeds for at most `122` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft15_001.lean, lines 19-84, SHA-256 80bd6d311d8f5c52630041ff8d844d145f53c96c33b82b422753d75a2cbe00df. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData15_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 122
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
