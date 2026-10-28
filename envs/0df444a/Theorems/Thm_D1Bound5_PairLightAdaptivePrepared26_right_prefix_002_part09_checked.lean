-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:49.110036+00:00
-- url     : https://prove2.me/theorems/343a7262-6e34-403f-a214-cfd92f6ca2b7
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 9
-- statement:
--   For prepared pair 26, right list, part 9, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 140 through 142; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_002Part09.lean, lines 7-11, SHA-256 dd68d0400225902cd38d22fbfbdd28a34cb4be5d78bfa7a46a37f74d4308b5a9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part09_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached002.drop 27) (rightRows002.drop 27) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
