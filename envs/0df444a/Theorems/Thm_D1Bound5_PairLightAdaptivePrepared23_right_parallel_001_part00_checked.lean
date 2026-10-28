-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:41.804457+00:00
-- url     : https://prove2.me/theorems/627fdc61-567b-4507-9cb9-453f74dd04bf
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 0
-- statement:
--   For prepared pair 23, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 92 through 103, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_001Part00.lean, lines 10-14, SHA-256 874f981fe07b81939487499a04a97015505b3707cd4852de00f05cc4c551a486. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 92) (PairLightPrepared23.rightRows.drop 92) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
