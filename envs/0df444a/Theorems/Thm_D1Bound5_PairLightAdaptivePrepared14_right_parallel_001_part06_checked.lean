-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:04.516101+00:00
-- url     : https://prove2.me/theorems/0251b5de-e119-4e82-9814-74f6483ddfc4
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 6
-- statement:
--   For prepared pair 14, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 160 through 171, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_001Part06.lean, lines 10-14, SHA-256 6a7ae79a2472d81b58ca5845dab97270bbc73a1858e2a5c859deeaaf606bd6db. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part06_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 160) (PairLightPrepared14.rightRows.drop 160) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
