-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:37.957395+00:00
-- url     : https://prove2.me/theorems/78173d01-c741-4d25-8181-cb8c39458b88
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 3
-- statement:
--   For prepared pair 36, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 323 through 334, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part03.lean, lines 10-14, SHA-256 9bca01bc0a1270850f6f67c66b8c9539e9d00ff29f84a2c5272a924a676114a9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 323) (PairLightPrepared36.rightRows.drop 323) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
