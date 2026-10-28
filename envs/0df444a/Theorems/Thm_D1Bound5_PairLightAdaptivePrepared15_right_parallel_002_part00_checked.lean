-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:31.982544+00:00
-- url     : https://prove2.me/theorems/83b6b4d8-cc39-487e-8382-99ca3eb8b4c6
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 0
-- statement:
--   For prepared pair 15, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 214 through 225, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part00.lean, lines 10-14, SHA-256 e52aaaf440f1506a1e063d42cab5aec7bff1033f3afcb6873a471b01d5a00096. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 214) (PairLightPrepared15.rightRows.drop 214) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
