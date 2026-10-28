-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:04.841912+00:00
-- url     : https://prove2.me/theorems/eef480b9-a1ad-4eea-a6ec-7d309bbc1e8b
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 3
-- statement:
--   For prepared pair 6, right list, part 3, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 175 through 188, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_002Part03.lean, lines 11-16, SHA-256 4abfde42d0fee6b49cce12d864ce3de4fe3b5de886e37963f817ea9dd03ab5e9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 14
      (PairLightPrepared6.rightCached.drop 175)
      (PairLightPrepared6.rightRows.drop 175) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
