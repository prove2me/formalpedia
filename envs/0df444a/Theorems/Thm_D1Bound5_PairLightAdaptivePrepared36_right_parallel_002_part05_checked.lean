-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:53.586983+00:00
-- url     : https://prove2.me/theorems/ac54fcf3-432a-4a28-823a-c4ef63f0b7bb
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 5
-- statement:
--   For prepared pair 36, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 227 through 238, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_002Part05.lean, lines 10-14, SHA-256 fec5a5c0a6a3bf227a37ab57618042ad6ffd7cfc85268386d2c731fa8656aac7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_002_part05_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 227) (PairLightPrepared36.rightRows.drop 227) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
