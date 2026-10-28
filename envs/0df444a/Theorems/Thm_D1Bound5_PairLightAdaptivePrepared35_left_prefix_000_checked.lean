-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:39.33598+00:00
-- url     : https://prove2.me/theorems/53dc6aac-10d5-4ce4-ad85-6442c7b0e088
-- title:
--   Selected-floor prefix certificate for prepared pair 35, left list
-- statement:
--   For prepared pair 35, left list, the selected-floor certificate succeeds for at most `132` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Heads 0 through 131; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft35_000.lean, lines 13-43, SHA-256 070be753a48c164ef2c68d8480b40efeb6ce7f91e3b4ec19d0b4380c2946fe6b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 132
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
