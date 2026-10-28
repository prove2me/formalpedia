-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:03.375834+00:00
-- url     : https://prove2.me/theorems/e663f391-9e61-4477-91a1-1deacb60ec6f
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 3
-- statement:
--   For prepared pair 5, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 36 through 47, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_000Part03.lean, lines 11-16, SHA-256 aa2b99526591d288119f0af089341354c6f6a3ddf04d5b9546805ed3e3995f93. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 12
      (PairLightPrepared5.rightCached.drop 36)
      (PairLightPrepared5.rightRows.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
