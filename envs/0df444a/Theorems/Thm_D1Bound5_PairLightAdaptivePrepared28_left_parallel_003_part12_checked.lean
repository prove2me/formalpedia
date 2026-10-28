-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_003_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:06.944986+00:00
-- url     : https://prove2.me/theorems/8088ba15-a493-4e05-af8c-4afdf638c46a
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 12
-- statement:
--   For prepared pair 28, left list, part 12, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 479 through 490, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_003Part12.lean, lines 10-14, SHA-256 8e927d7f39fe56369b93b061469ec35e4d47cd5eedad297ff22931e4c77fae6f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part12_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 479) (PairLightPrepared28.leftRows.drop 479) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
