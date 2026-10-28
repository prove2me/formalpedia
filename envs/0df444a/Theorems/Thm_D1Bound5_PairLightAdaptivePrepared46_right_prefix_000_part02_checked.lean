-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:12.011773+00:00
-- url     : https://prove2.me/theorems/b7d01762-4a37-4ad1-a778-8117f268787d
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list, part 2
-- statement:
--   For prepared pair 46, right list, part 2, the selected-floor certificate succeeds for at most `22` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 36 through 57, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_000Part02.lean, lines 7-11, SHA-256 b9ae5d5a0c71acaf3d083e5d139f9f39c7cd9bd6f424c43c941895937f3b91ff. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 22
      (rightCached000.drop 36) (rightRows000.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
