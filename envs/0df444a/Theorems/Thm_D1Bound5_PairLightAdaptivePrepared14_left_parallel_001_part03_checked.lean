-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:42.397114+00:00
-- url     : https://prove2.me/theorems/cb07503f-8c24-4e4a-be8f-2566533985da
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 3
-- statement:
--   For prepared pair 14, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 124 through 135, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_001Part03.lean, lines 10-14, SHA-256 ab6e471ba15251739b5912f02480ba7b876db120a7b0978e907566965324d598. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 124) (PairLightPrepared14.leftRows.drop 124) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
