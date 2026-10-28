-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:23.931915+00:00
-- url     : https://prove2.me/theorems/d9b985ba-2cdc-44d8-b822-68b75422bae6
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 14
-- statement:
--   For prepared pair 26, left list, part 14, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 155 through 157; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part14.lean, lines 7-11, SHA-256 476562ee936c12846f8f3aba7003da303a47c1f69eee3c96d3bca3b19585538e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part14_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 42) (leftRows002.drop 42) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
