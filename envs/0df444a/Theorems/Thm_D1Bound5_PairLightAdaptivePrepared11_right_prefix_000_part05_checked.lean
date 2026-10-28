-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:06.416964+00:00
-- url     : https://prove2.me/theorems/75bc82cc-78a4-4f3d-b118-cc51ec5a3ec3
-- title:
--   Selected-floor prefix certificate for prepared pair 11, right list, part 5
-- statement:
--   For prepared pair 11, right list, part 5, the selected-floor certificate succeeds for at most `30` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 108 through 137, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight11_000Part05.lean, lines 7-11, SHA-256 4e1a9bded087196aff74c1c42342f1f15ca99c99e6d65a6dd8e5eb95859baa43. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 30
      (rightCached000.drop 108) (rightRows000.drop 108) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
