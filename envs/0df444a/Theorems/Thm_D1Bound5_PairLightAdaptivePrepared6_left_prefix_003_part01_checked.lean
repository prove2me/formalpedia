-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_003_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_003_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:13.705634+00:00
-- url     : https://prove2.me/theorems/758681ec-e726-44e2-8778-3d84ec09bb5c
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 1
-- statement:
--   For prepared pair 6, left list, part 1, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 231 through 246, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_003Part01.lean, lines 11-16, SHA-256 d3bdc589549713c8bf70c2c1ffa339bfe5ceb57c82ba64f872649a67b661770f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_003_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 16
      (PairLightPrepared6.leftCached.drop 231)
      (PairLightPrepared6.leftRows.drop 231) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
