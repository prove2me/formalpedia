-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_003_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:59.779715+00:00
-- url     : https://prove2.me/theorems/8684a9dd-d009-4959-a261-ed2c8ea09c36
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 7
-- statement:
--   For prepared pair 28, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 419 through 430, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_003Part07.lean, lines 10-14, SHA-256 37005db4b69f747cc239b608e7e6c9a7dc7fe3c05c7c26a27adf663886d2c511. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 419) (PairLightPrepared28.leftRows.drop 419) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
