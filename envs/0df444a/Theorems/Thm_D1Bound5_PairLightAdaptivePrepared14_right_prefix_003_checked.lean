-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:35.278+00:00
-- url     : https://prove2.me/theorems/2f6e9515-8ddb-4a3c-ac16-93ccdf708f42
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list
-- statement:
--   For prepared pair 14, right list, the selected-floor certificate succeeds for at most `79` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight14_003.lean, lines 15-56, SHA-256 7c3a3c942d8b5d656c3f69cd726d8cd60bf7ed055845139c38afd7eee0b72280. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 79
      rightCached003 rightRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
