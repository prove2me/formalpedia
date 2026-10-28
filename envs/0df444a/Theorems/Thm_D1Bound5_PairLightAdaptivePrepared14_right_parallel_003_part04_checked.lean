-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_003_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:45.609401+00:00
-- url     : https://prove2.me/theorems/c6c03619-7a52-49bf-b2f0-0f816512a641
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 4
-- statement:
--   For prepared pair 14, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 465 through 476, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_003Part04.lean, lines 10-14, SHA-256 30a756caa632451ee535f3a62a73b193288a9a73020c0fb7c7bce7de0573d1ae. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part04_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 465) (PairLightPrepared14.rightRows.drop 465) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
