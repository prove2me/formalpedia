-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:24.122762+00:00
-- url     : https://prove2.me/theorems/8f3dc09e-914b-452f-ac65-f5216fd64805
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list
-- statement:
--   For prepared pair 14, left list, the selected-floor certificate succeeds for at most `217` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft14_002.lean, lines 27-140, SHA-256 a1955d043e37378ebc5d110c44f857b5d1f8b5593d768398f13c7f28087c3b6c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 217
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
