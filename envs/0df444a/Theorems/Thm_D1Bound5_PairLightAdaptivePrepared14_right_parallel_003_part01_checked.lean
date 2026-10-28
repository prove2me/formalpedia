-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_003_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:45.026802+00:00
-- url     : https://prove2.me/theorems/3959cd51-25fb-4820-9ad6-942557e04aeb
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 1
-- statement:
--   For prepared pair 14, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 429 through 440, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_003Part01.lean, lines 10-14, SHA-256 e1008d1d6baca4b923d165a15cd5610e5574eedb85f77c55ccff1b88f5b19d94. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part01_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 429) (PairLightPrepared14.rightRows.drop 429) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
