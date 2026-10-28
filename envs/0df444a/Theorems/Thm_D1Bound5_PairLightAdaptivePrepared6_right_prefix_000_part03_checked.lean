-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:07.943896+00:00
-- url     : https://prove2.me/theorems/f0bb1858-2796-4efe-ac4b-86d4734b53d7
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 3
-- statement:
--   For prepared pair 6, right list, part 3, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 31 through 41, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_000Part03.lean, lines 11-16, SHA-256 2e0524870b23cc23fdd23a45cb0e336d8a03329931afa7c54b7120b8c416c266. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 11
      (PairLightPrepared6.rightCached.drop 31)
      (PairLightPrepared6.rightRows.drop 31) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
