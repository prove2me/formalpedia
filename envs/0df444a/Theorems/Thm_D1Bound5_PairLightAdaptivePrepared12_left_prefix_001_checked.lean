-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:15.970924+00:00
-- url     : https://prove2.me/theorems/9e0216ab-c141-446e-ae3a-62cea1a3bc5e
-- title:
--   Selected-floor prefix certificate for prepared pair 12, left list
-- statement:
--   For prepared pair 12, left list, the selected-floor certificate succeeds for at most `221` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Heads 138 through 358; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft12_001.lean, lines 11-29, SHA-256 695b77eff85bbb00fae304cd7603f14c1e278d372f8e1f2fc93c31c9e974befa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 221
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
