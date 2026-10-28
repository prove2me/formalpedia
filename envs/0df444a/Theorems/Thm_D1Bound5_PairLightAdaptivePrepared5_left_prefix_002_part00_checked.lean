-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:22.761979+00:00
-- url     : https://prove2.me/theorems/0f1a68e1-167a-436e-8a81-f7e7c83855ad
-- title:
--   Selected-floor prefix certificate for prepared pair 5, left list, part 0
-- statement:
--   For prepared pair 5, left list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 269 through 292, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft5_002Part00.lean, lines 11-16, SHA-256 4c74dfcb0950632d711118eeb199eea98668d6246698b051934cf95a70efb781. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.leftCached.drop 269)
      (PairLightPrepared5.leftRows.drop 269) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
