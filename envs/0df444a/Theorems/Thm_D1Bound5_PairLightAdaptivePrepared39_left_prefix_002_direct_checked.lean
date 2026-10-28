-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:40:21.02845+00:00
-- url     : https://prove2.me/theorems/d70456c4-e11d-42d4-b818-4798d9410a88
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list
-- statement:
--   For prepared pair 39, left list, the selected-floor certificate succeeds for at most `225` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft39Prefix002.lean, lines 17-76, SHA-256 77461f86f10826cd16747d0010fa07adbdb733c785fe10d19ab73f06bfeb388e. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 225
      (PairLightPrepared39.leftCached.drop 233) (PairLightPrepared39.leftRows.drop 233) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared39
end
