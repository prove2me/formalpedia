-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:49:35.503287+00:00
-- url     : https://prove2.me/theorems/537be2cd-0f77-4a77-990c-f9d6af2fd17a
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list
-- statement:
--   For prepared pair 23, right list, the selected-floor certificate succeeds for at most `92` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight23_000.lean, lines 16-63, SHA-256 b2f13250d3439acb0d6977de052005cc484de7047aac1104781a74c7e57ca607. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 92
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
