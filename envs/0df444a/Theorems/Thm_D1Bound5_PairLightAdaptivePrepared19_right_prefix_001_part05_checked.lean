-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:02.316176+00:00
-- url     : https://prove2.me/theorems/d4ca6f73-306c-4e13-b1db-5292054043d6
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 5
-- statement:
--   For prepared pair 19, right list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 221 through 244, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_001Part05.lean, lines 11-16, SHA-256 1c2b914131772be65d1b30b581fe100e8f3935caae8bbf542c33cf4ec199e4de. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 221)
      (PairLightPrepared19.rightRows.drop 221) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
