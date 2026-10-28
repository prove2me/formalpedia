-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:44.66907+00:00
-- url     : https://prove2.me/theorems/8e2fb7bb-3e6b-4d9a-92b7-2b31893602f7
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list
-- statement:
--   For prepared pair 6, right list, the selected-floor certificate succeeds for at most `83` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_002.lean, lines 15-50, SHA-256 49d67e3e11c5d538dd2699d8b69bdb6a8791ed93c0f3de78389a48d5a9eda275. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 83
      rightCached002 rightRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
