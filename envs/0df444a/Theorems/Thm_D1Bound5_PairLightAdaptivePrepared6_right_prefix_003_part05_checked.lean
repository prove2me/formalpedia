-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:08.960899+00:00
-- url     : https://prove2.me/theorems/1fe29c11-0835-4479-bc29-c8b8293556ca
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 5
-- statement:
--   For prepared pair 6, right list, part 5, the selected-floor certificate succeeds for at most `19` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 301 through 319, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_003Part05.lean, lines 11-16, SHA-256 30a494dcedc9b25bf4757d53d21747ed603741ade0ae64d3010786a27e70802c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 19
      (PairLightPrepared6.rightCached.drop 301)
      (PairLightPrepared6.rightRows.drop 301) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
