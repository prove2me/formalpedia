-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:38.20635+00:00
-- url     : https://prove2.me/theorems/8f825edd-f690-4b03-8f33-9460b78bf175
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 1
-- statement:
--   For prepared pair 23, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 103 through 114, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_001Part01.lean, lines 10-14, SHA-256 9d503857d166717b8713bf43b29a964a5f06de7e1d5e5760343207dabbcaef34. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 103) (PairLightPrepared23.leftRows.drop 103) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
