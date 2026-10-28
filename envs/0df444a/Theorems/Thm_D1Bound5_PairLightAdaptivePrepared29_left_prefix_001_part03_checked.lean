-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:21.104324+00:00
-- url     : https://prove2.me/theorems/d5835a79-2721-49ea-8851-92c1b667b456
-- title:
--   Selected-floor prefix certificate for prepared pair 29, left list, part 3
-- statement:
--   For prepared pair 29, left list, part 3, the selected-floor certificate succeeds for at most `105` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 275 through 379, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft29_001Part03.lean, lines 7-11, SHA-256 1461b6b07f04731fe09312929f14421be71d74a32f1fa998ad7e9ce0a2d97c2b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 105
      (leftCached001.drop 149) (leftRows001.drop 149) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
