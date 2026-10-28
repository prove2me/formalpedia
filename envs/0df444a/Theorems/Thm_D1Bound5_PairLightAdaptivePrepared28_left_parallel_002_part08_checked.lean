-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_002_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:41.852183+00:00
-- url     : https://prove2.me/theorems/f3b4adb6-e8b3-46f5-8331-b1a2781f32a3
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 8
-- statement:
--   For prepared pair 28, left list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 280 through 291, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_002Part08.lean, lines 10-14, SHA-256 e1c0e60f9a8f0df83ee71f71774bb8c9ba316865d84df12b29610d4be0611f8c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 280) (PairLightPrepared28.leftRows.drop 280) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
