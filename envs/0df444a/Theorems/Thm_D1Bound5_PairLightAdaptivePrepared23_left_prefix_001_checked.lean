-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:51:03.824111+00:00
-- url     : https://prove2.me/theorems/71a970f1-6f6b-461a-9a33-f3cabe270264
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list
-- statement:
--   For prepared pair 23, left list, the selected-floor certificate succeeds for at most `121` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft23_001.lean, lines 19-84, SHA-256 41de77fee241508c8903206ad854eefb8e87cec101e457b202ae88c0b224c0e3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 121
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
