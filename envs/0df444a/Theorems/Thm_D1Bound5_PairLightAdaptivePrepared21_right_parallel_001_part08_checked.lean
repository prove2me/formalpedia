-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:56.100897+00:00
-- url     : https://prove2.me/theorems/115cc6ce-b868-4317-b323-16dff9cb26c4
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 8
-- statement:
--   For prepared pair 21, right list, part 8, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 178 through 183, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_001Part08.lean, lines 10-14, SHA-256 10c5809c80312a985dc486523e6ee339f02352c021e1ae9d0b1427c5a2f92dfe. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 6
      (PairLightPrepared21.rightCached.drop 178) (PairLightPrepared21.rightRows.drop 178) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
