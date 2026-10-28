-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:22.77779+00:00
-- url     : https://prove2.me/theorems/11aaa316-fe17-49cb-8b31-35082a4e68bc
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 5
-- statement:
--   For prepared pair 3, left list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 232 through 255, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_001Part05.lean, lines 9-14, SHA-256 214c843ea7fbdfc555bab40522fd3614c981cadc20bb75be52dfbb10111b0b02. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.leftCached.drop 232)
      (PairLightPrepared3.leftRows.drop 232) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
