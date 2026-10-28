-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:17.890362+00:00
-- url     : https://prove2.me/theorems/4d0fda46-06a1-440d-a31c-5b49bbe11802
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 2
-- statement:
--   For prepared pair 6, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 87 through 98, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_001Part02.lean, lines 11-16, SHA-256 4e9d9a25eed93886cc69728e176552ba4047c92647fe31b725df06676b3b871d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 12
      (PairLightPrepared6.rightCached.drop 87)
      (PairLightPrepared6.rightRows.drop 87) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
