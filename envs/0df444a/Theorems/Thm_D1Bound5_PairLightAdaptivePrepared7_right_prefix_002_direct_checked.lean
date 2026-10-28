-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:31.083854+00:00
-- url     : https://prove2.me/theorems/a3a43a71-4ebd-4d51-bef4-1bfe433181c4
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list
-- statement:
--   For prepared pair 7, right list, the selected-floor certificate succeeds for at most `158` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight7Prefix002.lean, lines 14-55, SHA-256 88109e2ce5ce1865d884b270a8cac1d914b19b59a49113f32fb961f3e0606ac3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 158
      (PairLightPrepared7.rightCached.drop 272) (PairLightPrepared7.rightRows.drop 272) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared7
end
