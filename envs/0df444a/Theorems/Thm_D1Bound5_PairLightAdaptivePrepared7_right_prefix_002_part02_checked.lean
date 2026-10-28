-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:40.196573+00:00
-- url     : https://prove2.me/theorems/15fbaa51-6ec7-4acf-9368-772f1d84c323
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 2
-- statement:
--   For prepared pair 7, right list, part 2, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 320 through 343, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_002Part02.lean, lines 11-16, SHA-256 ca869b5bcfc06fcf7edeaae1c2a95cb98c2b6cccd0e0c273dc8e5a1391a41e2c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.rightCached.drop 320)
      (PairLightPrepared7.rightRows.drop 320) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
