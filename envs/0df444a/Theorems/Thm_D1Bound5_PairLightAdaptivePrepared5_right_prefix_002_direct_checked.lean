-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:58.570821+00:00
-- url     : https://prove2.me/theorems/0fe5c714-0d88-46b2-94c3-b4ecabea5c21
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list
-- statement:
--   For prepared pair 5, right list, the selected-floor certificate succeeds for at most `158` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight5Prefix002.lean, lines 14-55, SHA-256 39498acf5c222b15acf9e950bd3a86ac0d48b4988638824a535b74c4144710df. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 158
      (PairLightPrepared5.rightCached.drop 272) (PairLightPrepared5.rightRows.drop 272) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared5
end
