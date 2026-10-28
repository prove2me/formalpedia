-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_004_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:09.816486+00:00
-- url     : https://prove2.me/theorems/a0389abc-8a21-4d0a-8b7a-a2038dd9e5d7
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 6
-- statement:
--   For prepared pair 6, left list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 466 through 468, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_004Part06.lean, lines 11-16, SHA-256 5af8719828a2e9983a4281d787e85693da5ac5b5e724d75192016e78f599140b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 3
      (PairLightPrepared6.leftCached.drop 466)
      (PairLightPrepared6.leftRows.drop 466) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
