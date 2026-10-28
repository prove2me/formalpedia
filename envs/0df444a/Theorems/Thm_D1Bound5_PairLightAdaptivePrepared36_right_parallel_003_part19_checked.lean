-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part19_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part19_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:30.2244+00:00
-- url     : https://prove2.me/theorems/0f9445d4-d14b-43c5-9fa0-8b6fd477853e
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 19
-- statement:
--   For prepared pair 36, right list, part 19, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 515 through 526, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part19.lean, lines 10-14, SHA-256 7c85ad0d6319992292f030c0764522038fcd46f544dece31f802aa27a3fb9da4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part19_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 515) (PairLightPrepared36.rightRows.drop 515) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
