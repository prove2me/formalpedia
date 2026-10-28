-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:33.138787+00:00
-- url     : https://prove2.me/theorems/9e87789c-071a-4ef7-ad5c-5f7479ad7547
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list, part 2
-- statement:
--   For prepared pair 46, left list, part 2, the selected-floor certificate succeeds for at most `22` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 36 through 57, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_000Part02.lean, lines 7-11, SHA-256 cf0d7aa86854c4e1a45b2ce3968e8c94a3781bf6c0b7abe271b2ad6471aa2f85. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 22
      (leftCached000.drop 36) (leftRows000.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
