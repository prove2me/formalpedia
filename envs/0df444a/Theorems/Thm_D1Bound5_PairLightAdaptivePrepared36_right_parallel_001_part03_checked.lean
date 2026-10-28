-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:18.313552+00:00
-- url     : https://prove2.me/theorems/6d621d67-45ee-4d8b-917a-55d32ddd034a
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 3
-- statement:
--   For prepared pair 36, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 112 through 123, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_001Part03.lean, lines 10-14, SHA-256 95b0496b24cecdd4c373b84b7a968123a6ca69a5589a217bd2f5bb86e82a923b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 112) (PairLightPrepared36.rightRows.drop 112) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
