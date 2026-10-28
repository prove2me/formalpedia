-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:01.930126+00:00
-- url     : https://prove2.me/theorems/d9712d49-5d43-41f0-8338-8cb5eadd8d82
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 4
-- statement:
--   For prepared pair 8, left list, part 4, the selected-floor certificate succeeds for at most `28` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 465 through 492, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_005Part04.lean, lines 11-16, SHA-256 3eb816f7327ae322fa3cb6df0dcb4460cbda6f91b80d2478110bdb11d21b0cf0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 28
      (PairLightPrepared8.leftCached.drop 465)
      (PairLightPrepared8.leftRows.drop 465) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
