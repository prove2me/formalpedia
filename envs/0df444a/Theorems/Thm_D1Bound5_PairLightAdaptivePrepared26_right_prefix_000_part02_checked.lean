-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:14.644958+00:00
-- url     : https://prove2.me/theorems/de043250-1b71-45aa-8a18-09ccef96f475
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 2
-- statement:
--   For prepared pair 26, right list, part 2, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 6 through 8 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_000Part02.lean, lines 7-11, SHA-256 1973d53a33ffba5309c0bd553bdac1a93e2a615d82df2251ff37de4c59cbc58f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached000.drop 6) (rightRows000.drop 6) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
