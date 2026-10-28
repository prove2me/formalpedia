-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:52.171518+00:00
-- url     : https://prove2.me/theorems/b7096785-0721-4229-b30d-ead28a2edc5c
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 6
-- statement:
--   For prepared pair 36, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 359 through 370, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part06.lean, lines 10-14, SHA-256 ba806388e2429b8d6b9061910fc84cb3dd8b582a803ba48978d735449cb7085f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part06_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 359) (PairLightPrepared36.rightRows.drop 359) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
