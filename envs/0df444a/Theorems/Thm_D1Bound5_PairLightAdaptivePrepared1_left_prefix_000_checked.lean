-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:47.796887+00:00
-- url     : https://prove2.me/theorems/507ce695-c3a5-4f7c-828d-c36fe52a4258
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list
-- statement:
--   For prepared pair 1, left list, the selected-floor certificate succeeds for at most `137` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Heads 0 through 136; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_000.lean, lines 14-50, SHA-256 a76978b4b387c3c46156fe93511d1db9cd3e463fddb79d1f0769c33d821ea278. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 137
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
