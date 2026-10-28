-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:32.153542+00:00
-- url     : https://prove2.me/theorems/f5e1268f-74d6-458f-a07a-0cb9c6de2ecc
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 6
-- statement:
--   For prepared pair 14, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 274 through 285, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_002Part06.lean, lines 10-14, SHA-256 540dd5122b56c12ebc19988316b6a299a113e4e58c1fc5f2a70a826cb7096c66. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part06_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 274) (PairLightPrepared14.rightRows.drop 274) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
