-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:04.792545+00:00
-- url     : https://prove2.me/theorems/7868aeb5-85de-4a58-9e13-0459b24d8cf8
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 10
-- statement:
--   For prepared pair 36, right list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 407 through 418, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part10.lean, lines 10-14, SHA-256 8fa5a9e69fcc9e9e1e5acab4c14c50f7f117fd1569c5b35485a090eeee52b09b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part10_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 407) (PairLightPrepared36.rightRows.drop 407) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
