-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:55.301211+00:00
-- url     : https://prove2.me/theorems/77366dff-f673-4248-9566-926f3dfc1d29
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 6
-- statement:
--   For prepared pair 15, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 164 through 175, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_001Part06.lean, lines 10-14, SHA-256 f39b20791a33947868aa8d4ceb9de129c0a3dc4b4e8d01d1fe7237bd72e45401. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part06_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 164) (PairLightPrepared15.leftRows.drop 164) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
