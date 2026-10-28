-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared9_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared9.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:17.224138+00:00
-- url     : https://prove2.me/theorems/d16f5fa6-a64b-42d7-87a8-01ebdeb13cba
-- title:
--   Selected-floor prefix certificate for prepared pair 9, right list
-- statement:
--   For prepared pair 9, right list, the selected-floor certificate succeeds for at most `219` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared9.sieve`. Heads 0 through 218; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight9_000.lean, lines 7-11, SHA-256 b62830ad50deb38e5fdb740e25ea7a36002d6e2c7d8f85035583c054c8328b56. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData9_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared9.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared9.sieve 219
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared9
end
