-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_004_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:50:16.665268+00:00
-- url     : https://prove2.me/theorems/6f000041-fcb0-4701-928b-5aa3e63193a8
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list
-- statement:
--   For prepared pair 10, left list, the selected-floor certificate succeeds for at most `191` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_004.lean, lines 13-36, SHA-256 9ab572c6328374ea5e6c8d3253bc0c11b2cd96c0514e50159991c7bb9aa5d915. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 191
      leftCached004 leftRows004 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
