-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:04.161534+00:00
-- url     : https://prove2.me/theorems/b060afd3-0f98-4162-a0af-23d60fdec43f
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 8
-- statement:
--   For prepared pair 28, left list, part 8, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 178 through 183, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_001Part08.lean, lines 10-14, SHA-256 bd3d0023c401702fba3308ead430519ddb4e699437a0aa87eaade4085345f962. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 6
      (PairLightPrepared28.leftCached.drop 178) (PairLightPrepared28.leftRows.drop 178) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
