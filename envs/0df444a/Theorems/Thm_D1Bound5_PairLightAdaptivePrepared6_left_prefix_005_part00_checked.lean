-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:01.568188+00:00
-- url     : https://prove2.me/theorems/67090092-6e7e-44e4-a946-b7f91190006d
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 0
-- statement:
--   For prepared pair 6, left list, part 0, the selected-floor certificate succeeds for at most `37` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 469 through 505, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_005Part00.lean, lines 11-16, SHA-256 8aee8e2d995e3eefde2a796daa102ae5fdd59c3c1d4d4d9f44e580efa2010c42. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 37
      (PairLightPrepared6.leftCached.drop 469)
      (PairLightPrepared6.leftRows.drop 469) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
