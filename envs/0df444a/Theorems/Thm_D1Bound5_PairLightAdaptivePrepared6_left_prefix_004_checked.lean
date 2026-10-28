-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_004_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:46.821312+00:00
-- url     : https://prove2.me/theorems/4164aef2-ab10-4d20-acc4-6e91e993a7ef
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list
-- statement:
--   For prepared pair 6, left list, the selected-floor certificate succeeds for at most `151` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_004.lean, lines 16-57, SHA-256 207ba73a18bbb0ab277bb1c8707a8a0d1ee9177939958d886e83832407e206ef. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 151
      leftCached004 leftRows004 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
