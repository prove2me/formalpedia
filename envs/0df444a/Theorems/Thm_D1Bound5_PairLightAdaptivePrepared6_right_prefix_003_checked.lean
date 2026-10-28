-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:39.98875+00:00
-- url     : https://prove2.me/theorems/c5c67b95-b03a-4738-9dde-cf09e533bf62
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list
-- statement:
--   For prepared pair 6, right list, the selected-floor certificate succeeds for at most `103` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_003.lean, lines 16-57, SHA-256 69a109d1b49c8f0f60ba9eeac626a4db6669cebaba5ea252b1c9c29160de9182. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 103
      rightCached003 rightRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
