-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:49.315698+00:00
-- url     : https://prove2.me/theorems/4c187058-7590-410b-bead-432424a92807
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 13
-- statement:
--   For prepared pair 23, left list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 368 through 379, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_002Part13.lean, lines 10-14, SHA-256 c974ca1f53ec3f2b0a825f89a08a1df9c76aa95d0a024a4ad6786bfc8e546c73. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part13_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 368) (PairLightPrepared23.leftRows.drop 368) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
