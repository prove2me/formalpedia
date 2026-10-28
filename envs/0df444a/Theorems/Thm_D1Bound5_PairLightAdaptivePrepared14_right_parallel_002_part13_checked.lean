-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:50.837978+00:00
-- url     : https://prove2.me/theorems/7c5e7fcb-d655-4c8b-8fed-74ae359a7c87
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 13
-- statement:
--   For prepared pair 14, right list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 358 through 369, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_002Part13.lean, lines 10-14, SHA-256 7b43325da3f19c474cf7ed4613d63eaad33549b416e06e7550735f758dadaac0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part13_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 358) (PairLightPrepared14.rightRows.drop 358) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
