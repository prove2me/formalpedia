-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:40:33.477586+00:00
-- url     : https://prove2.me/theorems/a8a92681-0b78-4f51-b53e-508b213225d2
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list
-- statement:
--   For prepared pair 39, right list, the selected-floor certificate succeeds for at most `98` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight39Prefix000.lean, lines 16-69, SHA-256 37ea66235db39d75431c4a8c6fd26684ce7e90d224a0f04386cdc50d64ddaa96. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 98
      (PairLightPrepared39.rightCached.drop 0) (PairLightPrepared39.rightRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared39
end
