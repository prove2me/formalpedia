-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_004_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:46.799123+00:00
-- url     : https://prove2.me/theorems/4f34d981-69a2-4e9f-9b46-bd3884f68bb1
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 2
-- statement:
--   For prepared pair 6, left list, part 2, the selected-floor certificate succeeds for at most `23` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 359 through 381, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_004Part02.lean, lines 11-16, SHA-256 85f1624cd5839fd5365f7f1169f6c5b260dc266feda34b62c75493c1fef81942. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 23
      (PairLightPrepared6.leftCached.drop 359)
      (PairLightPrepared6.leftRows.drop 359) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
