-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:33.341606+00:00
-- url     : https://prove2.me/theorems/812030e5-8715-4b4d-a2d1-45dd033c0721
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 13
-- statement:
--   For prepared pair 26, left list, part 13, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 152 through 154; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part13.lean, lines 7-11, SHA-256 669d0ff1623ffd6aacf41f8e04fb0dac29bb5299282986301775fb7861c4e819. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part13_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 39) (leftRows002.drop 39) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
