-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:09.033763+00:00
-- url     : https://prove2.me/theorems/4df94ffa-1c12-4293-bb56-9551f97cd3ca
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 2
-- statement:
--   For prepared pair 6, right list, part 2, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 20 through 30, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_000Part02.lean, lines 11-16, SHA-256 3e39277ef39edca0fd1fbc70d6ff9aefb1fcf8e2ad6fdd905b516bad5114d003. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 11
      (PairLightPrepared6.rightCached.drop 20)
      (PairLightPrepared6.rightRows.drop 20) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
