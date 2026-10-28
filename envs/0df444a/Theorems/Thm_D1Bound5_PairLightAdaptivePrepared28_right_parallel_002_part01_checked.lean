-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:11.446837+00:00
-- url     : https://prove2.me/theorems/d2bb1565-2d39-4dc1-b3e7-b4294cd37317
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 1
-- statement:
--   For prepared pair 28, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 196 through 207, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_002Part01.lean, lines 10-14, SHA-256 cec96bdf96d7b3fa81f3f1638f7d6dcea17d126e1da35837c5c7b2e145832edc. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 196) (PairLightPrepared28.rightRows.drop 196) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
