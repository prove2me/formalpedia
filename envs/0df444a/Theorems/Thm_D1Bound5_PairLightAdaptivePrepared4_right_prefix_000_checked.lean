-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:01.833226+00:00
-- url     : https://prove2.me/theorems/831b2cb5-65d6-402d-a082-07829dfd9fff
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list
-- statement:
--   For prepared pair 4, right list, the selected-floor certificate succeeds for at most `71` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_000.lean, lines 15-50, SHA-256 e21afb62c741fc043bccb274a35702a8d0717edab7e9cd11668d445b21570eb0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 71
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
