-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:24.606418+00:00
-- url     : https://prove2.me/theorems/811ba465-c0b2-4584-ab05-72d0be833eaf
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 5
-- statement:
--   For prepared pair 26, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 311 through 322; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_004Part05.lean, lines 7-11, SHA-256 947cb826a3d372e5b9fbdbdc45bfaae2f82aa76d8947dce841037f01b7d932c8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached004.drop 60) (rightRows004.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
