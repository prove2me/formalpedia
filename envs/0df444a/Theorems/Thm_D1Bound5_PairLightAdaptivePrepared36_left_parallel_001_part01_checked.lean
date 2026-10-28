-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:03.771982+00:00
-- url     : https://prove2.me/theorems/7ee63e4d-2e7d-4a04-a8bd-e6bcd911dfb2
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 1
-- statement:
--   For prepared pair 36, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 88 through 99, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_001Part01.lean, lines 10-14, SHA-256 2e891d9c015f7f68e14b38a9a79d27d9a9369c2ae68237733fc870c96dbd5788. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 88) (PairLightPrepared36.leftRows.drop 88) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
