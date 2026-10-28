-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_004_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:12.655069+00:00
-- url     : https://prove2.me/theorems/ec40a3d6-2282-4248-a9bb-015a2604d4a0
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 3
-- statement:
--   For prepared pair 6, left list, part 3, the selected-floor certificate succeeds for at most `25` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 382 through 406, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_004Part03.lean, lines 11-16, SHA-256 e3103148a6951c90d52b318984f2641aea2a35fae0dc886009d5117f56830fc3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 25
      (PairLightPrepared6.leftCached.drop 382)
      (PairLightPrepared6.leftRows.drop 382) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
