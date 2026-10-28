-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:56.487345+00:00
-- url     : https://prove2.me/theorems/a3c7292a-0fd1-4ac6-af97-ee698d157b41
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 8
-- statement:
--   For prepared pair 3, left list, part 8, the selected-floor certificate succeeds for at most `7` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 304 through 310, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_001Part08.lean, lines 9-14, SHA-256 a67c2736aed284a9e8f99829d7cebe4c4d493a009d6535af17bdc3ec685766d1. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_part08_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 7
      (PairLightPrepared3.leftCached.drop 304)
      (PairLightPrepared3.leftRows.drop 304) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
