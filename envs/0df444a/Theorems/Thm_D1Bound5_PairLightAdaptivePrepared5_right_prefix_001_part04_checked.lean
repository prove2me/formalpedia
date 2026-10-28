-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:19.910225+00:00
-- url     : https://prove2.me/theorems/255435d5-a69c-4c84-b429-34ecee7dc671
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 4
-- statement:
--   For prepared pair 5, right list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 202 through 225, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_001Part04.lean, lines 11-16, SHA-256 f0a028125ede17e93aa25927b4a50339a7d3b2c0a8170fab0c601482f8abc79b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.rightCached.drop 202)
      (PairLightPrepared5.rightRows.drop 202) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
