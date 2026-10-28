-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_002_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:44.333923+00:00
-- url     : https://prove2.me/theorems/35407ff1-3303-417b-9abb-635440b7648d
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 12
-- statement:
--   For prepared pair 26, right list, part 12, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 149 through 151; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_002Part12.lean, lines 7-11, SHA-256 97169164b7bb6e393df6165655333bc2089db44f6979535a10cd1757425b729d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part12_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached002.drop 36) (rightRows002.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
