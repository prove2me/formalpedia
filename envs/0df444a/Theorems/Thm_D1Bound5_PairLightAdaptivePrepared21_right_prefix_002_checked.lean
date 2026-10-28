-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:43.700483+00:00
-- url     : https://prove2.me/theorems/cdbcd66c-f281-4776-8fa6-bf69b1ee53fc
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list
-- statement:
--   For prepared pair 21, right list, the selected-floor certificate succeeds for at most `151` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight21_002.lean, lines 21-98, SHA-256 0ca7c8f2668bcef13dc8d10d08798c15b0355ea075c00d0efcc9bc1035d250ba. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData21_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 151
      rightCached002 rightRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
