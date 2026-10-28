-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:57.692486+00:00
-- url     : https://prove2.me/theorems/96561439-71f1-4d1a-acf8-6cb7ce58eccf
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 13
-- statement:
--   For prepared pair 36, right list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 443 through 454, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part13.lean, lines 10-14, SHA-256 71873bf2ee8a7195a82fd9b4c2129602b74ee079f00a3b2a4ef00407156d2f1b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part13_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 443) (PairLightPrepared36.rightRows.drop 443) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
