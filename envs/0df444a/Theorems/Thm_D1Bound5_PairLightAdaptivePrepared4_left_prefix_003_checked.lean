-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:49:53.201028+00:00
-- url     : https://prove2.me/theorems/94724795-e2d6-479e-9b0b-2268105c2f34
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list
-- statement:
--   For prepared pair 4, left list, the selected-floor certificate succeeds for at most `150` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_003.lean, lines 16-57, SHA-256 897ffd07b48b6ca751d16e02fc410e4f7a01b360394dc7694d9f4ac850c27b3a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 150
      leftCached003 leftRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
