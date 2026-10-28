-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part18_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part18_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:46.571694+00:00
-- url     : https://prove2.me/theorems/ae7fde82-e444-4015-8fd3-dc423461fc23
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 18
-- statement:
--   For prepared pair 36, right list, part 18, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 503 through 514, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part18.lean, lines 10-14, SHA-256 81bd78338a1309fe1dc62c8950a02c0f666c449aabf8aeac1fa8ebdb7d346618. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part18_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 503) (PairLightPrepared36.rightRows.drop 503) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
