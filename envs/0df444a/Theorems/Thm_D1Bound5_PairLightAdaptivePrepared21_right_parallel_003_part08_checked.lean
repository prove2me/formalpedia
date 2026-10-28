-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_003_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:54.792779+00:00
-- url     : https://prove2.me/theorems/e548db0d-99e5-4d59-a5ba-fb5e4f7fd8fa
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 8
-- statement:
--   For prepared pair 21, right list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 431 through 442, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_003Part08.lean, lines 10-14, SHA-256 5967adb001c0f7898f8b309654d6f374512270a915e7e4e931f68ee95537e5c4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 431) (PairLightPrepared21.rightRows.drop 431) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
