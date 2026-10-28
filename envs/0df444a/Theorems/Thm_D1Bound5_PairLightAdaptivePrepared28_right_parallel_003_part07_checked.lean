-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:41.567148+00:00
-- url     : https://prove2.me/theorems/af35a94e-960d-4127-b5a6-7e5c08d7fa7d
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 7
-- statement:
--   For prepared pair 28, right list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 419 through 430, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_003Part07.lean, lines 10-14, SHA-256 d12969f1ae34233b9824c0e611a2619bfdeb9958ad0a0e74e84b1bc307d3277d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 419) (PairLightPrepared28.rightRows.drop 419) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
