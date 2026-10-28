-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:15.993118+00:00
-- url     : https://prove2.me/theorems/18e0b8e7-ad43-4895-873d-68569bf2378f
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 5
-- statement:
--   For prepared pair 15, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 152 through 163, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_001Part05.lean, lines 10-14, SHA-256 9264204a42ef617623f3414d17a935f16e55aaba501c2ff72a320746f9f8f69d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part05_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 152) (PairLightPrepared15.leftRows.drop 152) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
