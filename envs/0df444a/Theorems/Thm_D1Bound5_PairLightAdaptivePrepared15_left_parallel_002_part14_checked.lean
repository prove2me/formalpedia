-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:56.861147+00:00
-- url     : https://prove2.me/theorems/e4e6f0c6-8a8a-49b0-9421-a426d319897a
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 14
-- statement:
--   For prepared pair 15, left list, part 14, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 382 through 393, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_002Part14.lean, lines 10-14, SHA-256 8c4430f6a86fb6d4ff5cf9be601b28ed228110de2d9d17c9140fac27a5565477. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part14_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 382) (PairLightPrepared15.leftRows.drop 382) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
