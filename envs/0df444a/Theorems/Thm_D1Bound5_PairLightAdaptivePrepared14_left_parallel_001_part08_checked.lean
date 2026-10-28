-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:27.216768+00:00
-- url     : https://prove2.me/theorems/25b1f10c-f965-4a6e-84f3-c49a0161d531
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 8
-- statement:
--   For prepared pair 14, left list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 184 through 195, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_001Part08.lean, lines 10-14, SHA-256 444282962f6f7e4269739f8155527b72751c2d802c65346ed2bb9e719ac2b356. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 184) (PairLightPrepared14.leftRows.drop 184) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
