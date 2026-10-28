-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:16.091733+00:00
-- url     : https://prove2.me/theorems/3711f40a-4774-4aec-a493-12cfc15469fd
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 5
-- statement:
--   For prepared pair 6, right list, part 5, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 53 through 63, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_000Part05.lean, lines 11-16, SHA-256 06bbae84e1c5da92e5001b935588ae97b683afac803ff814199b2f0190a6370f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 11
      (PairLightPrepared6.rightCached.drop 53)
      (PairLightPrepared6.rightRows.drop 53) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
