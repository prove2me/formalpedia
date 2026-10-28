-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_000_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:28.984629+00:00
-- url     : https://prove2.me/theorems/f9aea30e-285f-4a3e-ac27-3b0ab504a244
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 13
-- statement:
--   For prepared pair 26, right list, part 13, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 39 through 41 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_000Part13.lean, lines 7-11, SHA-256 92504c350b3b88116ae15b836295d09027ffc061c6343a815db257308b5ceed6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part13_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached000.drop 39) (rightRows000.drop 39) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
