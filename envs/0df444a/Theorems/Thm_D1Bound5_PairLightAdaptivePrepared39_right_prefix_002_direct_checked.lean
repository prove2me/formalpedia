-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:43.683761+00:00
-- url     : https://prove2.me/theorems/efc2c9ca-ef23-4abe-88c2-4059f8ec9621
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list
-- statement:
--   For prepared pair 39, right list, the selected-floor certificate succeeds for at most `220` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight39Prefix002.lean, lines 17-76, SHA-256 b340fce2a5c4b83657c7c3d3f7ca8bf92ad0edbe831b56b80044693cf028ecf8. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 220
      (PairLightPrepared39.rightCached.drop 236) (PairLightPrepared39.rightRows.drop 236) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared39
end
