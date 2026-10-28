-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:42.427194+00:00
-- url     : https://prove2.me/theorems/df3a230a-604f-4f93-8ecd-41cec4a2183d
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 5
-- statement:
--   For prepared pair 7, right list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 392 through 415, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_002Part05.lean, lines 11-16, SHA-256 d8ea109c0cad682b61533f3541ddb48070a87ad0ff767a0011de4a35ef057e3d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.rightCached.drop 392)
      (PairLightPrepared7.rightRows.drop 392) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
