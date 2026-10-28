-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_002_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:25.085861+00:00
-- url     : https://prove2.me/theorems/bf9bb581-fee9-4f2e-8387-5e76a781bfce
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 8
-- statement:
--   For prepared pair 26, right list, part 8, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 137 through 139; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_002Part08.lean, lines 7-11, SHA-256 ac7b121f6946590b9f6fb568cf88c96ce731848964c2ebf7e16809238ff4fc48. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached002.drop 24) (rightRows002.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
