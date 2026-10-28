-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_005_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_005_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:19.528637+00:00
-- url     : https://prove2.me/theorems/7f868bfd-354e-4809-8f9d-45eced27594d
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 8
-- statement:
--   For prepared pair 26, right list, part 8, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 432 through 442; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_005Part08.lean, lines 7-11, SHA-256 5927f493ff1a0ff20031355f31280b22635ba10e133fc00af52b75d6df7c02b5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_005_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 11
      (rightCached005.drop 96) (rightRows005.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
