-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:09.787984+00:00
-- url     : https://prove2.me/theorems/b4933dd9-4594-4ef5-86d6-d679ef149091
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 4
-- statement:
--   For prepared pair 6, right list, part 4, the selected-floor certificate succeeds for at most `18` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 283 through 300, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_003Part04.lean, lines 11-16, SHA-256 3cb7e46f2150929a1efe298f0c6a1b4841858e25136c9ecaaafae88f9b9bfb7b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 18
      (PairLightPrepared6.rightCached.drop 283)
      (PairLightPrepared6.rightRows.drop 283) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
