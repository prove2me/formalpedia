-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:12.790284+00:00
-- url     : https://prove2.me/theorems/8063fb15-3dc3-4094-b641-bcf254edde72
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 3
-- statement:
--   For prepared pair 6, right list, part 3, the selected-floor certificate succeeds for at most `25` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 386 through 410, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_004Part03.lean, lines 11-16, SHA-256 7c4708f86c0952ce8278841d66e74535ac16dc04b6642d3ef361e00f0cdb9e7d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 25
      (PairLightPrepared6.rightCached.drop 386)
      (PairLightPrepared6.rightRows.drop 386) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
