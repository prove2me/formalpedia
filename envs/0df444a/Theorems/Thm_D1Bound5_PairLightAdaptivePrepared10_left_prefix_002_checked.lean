-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:29.276831+00:00
-- url     : https://prove2.me/theorems/3cb14fde-6913-463e-9ed4-5979fb49a1ef
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list
-- statement:
--   For prepared pair 10, left list, the selected-floor certificate succeeds for at most `102` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_002.lean, lines 15-50, SHA-256 ff4e35483db806c650bee3a5b3e26d5ac4ae37fd5c9963c602aa4ec5a0614ef5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 102
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
