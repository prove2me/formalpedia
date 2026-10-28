-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:37.585622+00:00
-- url     : https://prove2.me/theorems/c5d8f3a5-be49-4809-8c21-cb7dd22f8c69
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list
-- statement:
--   For prepared pair 8, left list, the selected-floor certificate succeeds for at most `102` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_004.lean, lines 15-50, SHA-256 27c48ef5c6f43c2c37f95ae0d178c9724ae79e27e3f3772a09efd018bffe1f16. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 102
      leftCached004 leftRows004 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
