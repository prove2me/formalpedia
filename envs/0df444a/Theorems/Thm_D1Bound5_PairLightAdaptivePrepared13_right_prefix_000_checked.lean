-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared13_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared13.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:20.380751+00:00
-- url     : https://prove2.me/theorems/99813bed-707a-4559-846a-c25d970dbd28
-- title:
--   Selected-floor prefix certificate for prepared pair 13, right list
-- statement:
--   For prepared pair 13, right list, the selected-floor certificate succeeds for at most `248` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared13.sieve`. Heads 0 through 247; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight13_000.lean, lines 7-11, SHA-256 04c2f0e0567eef743efb4a656575531af7f2c29f1ca4503b4a22ae5c1fee6bb0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData13_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared13.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared13.sieve 248
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared13
end
