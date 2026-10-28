-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:17.845991+00:00
-- url     : https://prove2.me/theorems/ef20cf64-3c3b-4843-aa86-6900acfde03f
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 5
-- statement:
--   For prepared pair 6, right list, part 5, the selected-floor certificate succeeds for at most `15` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 203 through 217, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_002Part05.lean, lines 11-16, SHA-256 a72fef49f82e48bf260f975f2cd5275129c7ae7854b00cae4719eaaaf4052c04. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 15
      (PairLightPrepared6.rightCached.drop 203)
      (PairLightPrepared6.rightRows.drop 203) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
