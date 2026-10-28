-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_002_part22_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:28.517296+00:00
-- url     : https://prove2.me/theorems/6054dd21-313a-43a3-ab90-d9442db17dec
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 22
-- statement:
--   For prepared pair 30, left list, part 22, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 476 through 481, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_002Part22.lean, lines 10-14, SHA-256 b88a36e8a9b45560b3bf1f4da455792542e4486258e8e0c1f506648e19fe0d94. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part22_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 6
      (PairLightPrepared30.leftCached.drop 476) (PairLightPrepared30.leftRows.drop 476) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
