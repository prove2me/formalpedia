-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:42.23245+00:00
-- url     : https://prove2.me/theorems/dd060279-4afc-485e-9d07-2e6236cfdb78
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 3
-- statement:
--   For prepared pair 3, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 36 through 47, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_000Part03.lean, lines 9-14, SHA-256 a6f438ba4585b6d5b0f866458ecebdeb150bec7ce7f02d2ad2684bd1be480bda. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 12
      (PairLightPrepared3.leftCached.drop 36)
      (PairLightPrepared3.leftRows.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
