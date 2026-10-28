-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:15.70576+00:00
-- url     : https://prove2.me/theorems/2d5cfa18-e24a-4d12-9f8f-847e69451f87
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 4
-- statement:
--   For prepared pair 15, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 48 through 59, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_000Part04.lean, lines 10-14, SHA-256 cc19e38b63645b720c06cfc26ed19e842e38d50529c36549911a094f377b5819. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 48) (PairLightPrepared15.leftRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
