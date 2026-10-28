-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:28.175167+00:00
-- url     : https://prove2.me/theorems/ad956d00-8a74-4208-998c-3022f0c9e498
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 0
-- statement:
--   For prepared pair 15, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 214 through 225, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_002Part00.lean, lines 10-14, SHA-256 3a49508cc067f558bd75dcc5d607040e0fbeac82f8ba0d91e80cb8be695acc69. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 214) (PairLightPrepared15.leftRows.drop 214) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
