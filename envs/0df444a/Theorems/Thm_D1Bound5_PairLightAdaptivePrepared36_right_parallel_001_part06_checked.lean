-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:55.229361+00:00
-- url     : https://prove2.me/theorems/665cb299-70d1-4a22-a734-a2b2b9db175d
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 6
-- statement:
--   For prepared pair 36, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 148 through 159, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_001Part06.lean, lines 10-14, SHA-256 e5c9ee913c8cf6079d8f8f4769d5def2ad072526586bb0994a50f94030d276de. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part06_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 148) (PairLightPrepared36.rightRows.drop 148) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
