-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:37.421974+00:00
-- url     : https://prove2.me/theorems/d8db7a3b-382f-48db-92e7-71341cb4f19a
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list
-- statement:
--   For prepared pair 46, right list, the selected-floor certificate succeeds for at most `138` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Heads 0 through 137; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_000.lean, lines 14-50, SHA-256 74b78f8a14dc34d5a45569f136bdf3bb72bc92de5438f047d527bdcfebd7583d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 138
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
