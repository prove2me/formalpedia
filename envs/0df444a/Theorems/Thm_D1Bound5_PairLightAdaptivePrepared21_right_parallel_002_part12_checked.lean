-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_002_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:51.012795+00:00
-- url     : https://prove2.me/theorems/e564a6ba-d5e6-44ef-8ef7-9931a3be36cc
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 12
-- statement:
--   For prepared pair 21, right list, part 12, the selected-floor certificate succeeds for at most `7` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 328 through 334, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_002Part12.lean, lines 10-14, SHA-256 d26e30df0c075bf748a33e743992c353645ea365f436eb706c450515f0d66e1c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part12_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 7
      (PairLightPrepared21.rightCached.drop 328) (PairLightPrepared21.rightRows.drop 328) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
