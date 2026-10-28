-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:00.737905+00:00
-- url     : https://prove2.me/theorems/4e8309b7-1dd2-4a7c-a5e9-70bbec98b432
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 2
-- statement:
--   For prepared pair 28, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 106 through 117, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_001Part02.lean, lines 10-14, SHA-256 f21b14bbc4da2f9fb00439b5cbb6256a8fd678bfc1c965d58a439bfa71718eb6. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 106) (PairLightPrepared28.leftRows.drop 106) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
