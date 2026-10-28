-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_004_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:10.841994+00:00
-- url     : https://prove2.me/theorems/9f2189ea-e1bf-4380-a269-f6c1cfa14c37
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 4
-- statement:
--   For prepared pair 6, left list, part 4, the selected-floor certificate succeeds for at most `28` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 407 through 434, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_004Part04.lean, lines 11-16, SHA-256 826e90d4859191cf413137d4101081e06a0be5d2a1d5aa0a32f8e722c79eb91b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 28
      (PairLightPrepared6.leftCached.drop 407)
      (PairLightPrepared6.leftRows.drop 407) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
