-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:13.376111+00:00
-- url     : https://prove2.me/theorems/fdb70ec2-3958-4ef9-b3bc-9c3237f430ae
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 4
-- statement:
--   For prepared pair 39, left list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 193 through 216, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_001Part04.lean, lines 11-16, SHA-256 972bc74e30bf72aa566c481a312c733f1eb954dab255f91c8493d2192375c102. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.leftCached.drop 193)
      (PairLightPrepared39.leftRows.drop 193) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
