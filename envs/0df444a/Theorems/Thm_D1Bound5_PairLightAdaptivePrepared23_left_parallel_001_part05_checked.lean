-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:08.726183+00:00
-- url     : https://prove2.me/theorems/a9e5b57d-1f39-4fb5-babf-6b83d1537760
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 5
-- statement:
--   For prepared pair 23, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 151 through 162, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_001Part05.lean, lines 10-14, SHA-256 857982a9275d2f6a73e608c7371aea029ddc7d7e4dcf6b59bf494687f80be574. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 151) (PairLightPrepared23.leftRows.drop 151) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
