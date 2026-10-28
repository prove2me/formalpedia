-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:44.961832+00:00
-- url     : https://prove2.me/theorems/7013c474-e33e-43c7-8983-43064387dc04
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 3
-- statement:
--   For prepared pair 28, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 371 through 382, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_003Part03.lean, lines 10-14, SHA-256 d2c32616cc5fe27ce2452650167997a63ba66884b66ccaf41be13db3f947f520. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 371) (PairLightPrepared28.rightRows.drop 371) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
