-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part21_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part21_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:18.021848+00:00
-- url     : https://prove2.me/theorems/fb6377c8-45e4-4d7a-9307-3711db734627
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 21
-- statement:
--   For prepared pair 26, left list, part 21, the selected-floor certificate succeeds for at most `2` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 176 through 177; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part21.lean, lines 7-11, SHA-256 a5c2618228a3b205585d3776dacccc01c1992a181c90635eebd621e5f9bbeda9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part21_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 2
      (leftCached002.drop 63) (leftRows002.drop 63) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
