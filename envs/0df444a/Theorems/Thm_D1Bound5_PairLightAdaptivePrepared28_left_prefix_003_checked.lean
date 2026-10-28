-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:51:29.242658+00:00
-- url     : https://prove2.me/theorems/41990fe2-e1c3-474a-ad88-aea578f80210
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list
-- statement:
--   For prepared pair 28, left list, the selected-floor certificate succeeds for at most `189` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft28_003.lean, lines 24-119, SHA-256 3d0b7c5db021c45989b2462d240f6a1a210e2ec03df1d29e4c04bf14cb2b3ce0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 189
      leftCached003 leftRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
