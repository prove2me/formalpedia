-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:00.670982+00:00
-- url     : https://prove2.me/theorems/310ea141-8c80-46cb-a4ed-9ab00e592ec1
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 1
-- statement:
--   For prepared pair 15, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 226 through 237, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_002Part01.lean, lines 10-14, SHA-256 cc4db466cfaf63c4b7c89ad6320b046c6875170ed546a0376427d8b861b22010. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part01_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 226) (PairLightPrepared15.leftRows.drop 226) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
