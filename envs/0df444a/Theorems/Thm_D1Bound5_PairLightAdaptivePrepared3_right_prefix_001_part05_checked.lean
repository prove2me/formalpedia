-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:56:55.478135+00:00
-- url     : https://prove2.me/theorems/b33a0718-05e9-4023-851c-1647b3b748c1
-- title:
--   Selected-floor prefix certificate for prepared pair 3, right list, part 5
-- statement:
--   For prepared pair 3, right list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 231 through 254, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight3_001Part05.lean, lines 10-15, SHA-256 42cd290756f22a9601ce7fc3b8dd928c2295d592d101edea51605c955c1be20d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.rightCached.drop 231)
      (PairLightPrepared3.rightRows.drop 231) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
