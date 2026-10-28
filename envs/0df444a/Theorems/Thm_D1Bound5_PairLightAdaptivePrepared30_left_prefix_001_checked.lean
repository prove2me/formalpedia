-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:33.12014+00:00
-- url     : https://prove2.me/theorems/ad511e7c-1cf6-4459-812c-cf1badde9df7
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list
-- statement:
--   For prepared pair 30, left list, the selected-floor certificate succeeds for at most `121` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft30_001.lean, lines 19-84, SHA-256 12e35875b0d47dbe9fb0f4d2f118024915ae58012deedeed3877939a7347a965. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData30_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 121
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
