-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:14.116098+00:00
-- url     : https://prove2.me/theorems/f893bab6-0ba6-43a2-b7fd-eb49d0e51e13
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list
-- statement:
--   For prepared pair 39, left list, the selected-floor certificate succeeds for at most `136` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft39Prefix001.lean, lines 13-48, SHA-256 02dff31008c7f5b627efb398361fbff815e2f28de2bc295003fb5db14c848be7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 136
      (PairLightPrepared39.leftCached.drop 97) (PairLightPrepared39.leftRows.drop 97) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared39
end
