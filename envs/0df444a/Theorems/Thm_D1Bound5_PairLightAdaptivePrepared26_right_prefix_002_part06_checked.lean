-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:31.220477+00:00
-- url     : https://prove2.me/theorems/58794146-1552-4e69-a69e-7da47a159d0b
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 6
-- statement:
--   For prepared pair 26, right list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 131 through 133; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_002Part06.lean, lines 7-11, SHA-256 d2a46259ac9f23439eb05fda54babe35509d398d78d7a32f1841e1d1e97b1ce6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached002.drop 18) (rightRows002.drop 18) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
