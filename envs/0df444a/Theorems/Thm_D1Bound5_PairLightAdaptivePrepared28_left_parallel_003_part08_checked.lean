-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_003_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:17.527458+00:00
-- url     : https://prove2.me/theorems/edf8b88a-f325-49fe-bdff-5910f26b4723
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 8
-- statement:
--   For prepared pair 28, left list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 431 through 442, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_003Part08.lean, lines 10-14, SHA-256 a7a2bcd2a3ef63d806d20645d2ff1c00ada416a28657f6900a8f1427909e43fb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 431) (PairLightPrepared28.leftRows.drop 431) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
