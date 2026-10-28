-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:49.033566+00:00
-- url     : https://prove2.me/theorems/59b12abc-676b-4e74-90b1-fe7aecdf8029
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 7
-- statement:
--   For prepared pair 36, right list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 251 through 262, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_002Part07.lean, lines 10-14, SHA-256 64d518b0027295a3402bd7255281730af8779756f4e51e94f1135778d18b764f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_002_part07_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 251) (PairLightPrepared36.rightRows.drop 251) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
