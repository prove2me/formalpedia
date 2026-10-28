-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:12.604741+00:00
-- url     : https://prove2.me/theorems/59daa9e6-7d90-4802-896f-3bec52dc9143
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 8
-- statement:
--   For prepared pair 15, left list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 188 through 199, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_001Part08.lean, lines 10-14, SHA-256 0213a9a1341983e70563e41cd62492a6582c40d0200d0fad3a280ec0dfc0f692. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 188) (PairLightPrepared15.leftRows.drop 188) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
