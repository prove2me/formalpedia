-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_002_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:30.517812+00:00
-- url     : https://prove2.me/theorems/e014be35-a6b2-4edd-bb57-2b93fd3d6ffe
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 12
-- statement:
--   For prepared pair 30, left list, part 12, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 356 through 367, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_002Part12.lean, lines 10-14, SHA-256 4a48a6f9dab371f2e87683c5f897127a992dc7cd2c2487f9dcf199b298e2a4fe. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part12_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 356) (PairLightPrepared30.leftRows.drop 356) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
