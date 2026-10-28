-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:58.646286+00:00
-- url     : https://prove2.me/theorems/c3ddefc1-c5e5-43e9-b25a-3a2f22d13a90
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 0
-- statement:
--   For prepared pair 28, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 82 through 93, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_001Part00.lean, lines 10-14, SHA-256 b68b2d665469ed52c510f5fc28aed5997d8b173d8c86278054fba42a03bcab32. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 82) (PairLightPrepared28.leftRows.drop 82) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
