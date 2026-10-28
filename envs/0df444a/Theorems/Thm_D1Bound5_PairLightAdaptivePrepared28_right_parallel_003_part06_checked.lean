-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:01.147434+00:00
-- url     : https://prove2.me/theorems/02fcd3a2-4a63-46c7-91b2-4d7217238e71
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 6
-- statement:
--   For prepared pair 28, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 407 through 418, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_003Part06.lean, lines 10-14, SHA-256 db7216563bb2e6694c4d2831d3289a056fd7b39e6b024b34f7577ad61ed5a9ec. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 407) (PairLightPrepared28.rightRows.drop 407) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
