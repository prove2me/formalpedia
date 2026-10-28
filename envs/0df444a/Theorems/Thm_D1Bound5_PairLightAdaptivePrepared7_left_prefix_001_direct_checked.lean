-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:37:52.452992+00:00
-- url     : https://prove2.me/theorems/ac0c3895-1882-4eb8-99d4-f7038a8ad60c
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list
-- statement:
--   For prepared pair 7, left list, the selected-floor certificate succeeds for at most `163` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft7Prefix001.lean, lines 14-55, SHA-256 baeda0f07e9076124f78228355a40d8a5c39b6c37ebf3c878cbd10ff493aacf8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 163
      (PairLightPrepared7.leftCached.drop 105) (PairLightPrepared7.leftRows.drop 105) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared7
end
