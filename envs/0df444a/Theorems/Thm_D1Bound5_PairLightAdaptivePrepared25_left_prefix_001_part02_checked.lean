-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:56.394025+00:00
-- url     : https://prove2.me/theorems/f3da32c4-1727-4a3f-9aa6-021ea23b4eda
-- title:
--   Selected-floor prefix certificate for prepared pair 25, left list, part 2
-- statement:
--   For prepared pair 25, left list, part 2, the selected-floor certificate succeeds for at most `65` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 210 through 274, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft25_001Part02.lean, lines 7-11, SHA-256 4108abac1e4b490421fc8509cdf9cb31d5376b8256c1030c7fd77cbce4cee050. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 65
      (leftCached001.drop 84) (leftRows001.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
