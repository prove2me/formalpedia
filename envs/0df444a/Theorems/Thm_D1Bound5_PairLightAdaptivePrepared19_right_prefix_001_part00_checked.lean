-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:26.508717+00:00
-- url     : https://prove2.me/theorems/a6d43d14-3f02-4cdd-9c23-5e7a1856b05f
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 0
-- statement:
--   For prepared pair 19, right list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 101 through 124, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_001Part00.lean, lines 11-16, SHA-256 4cc5d2f9eecdc7cf6c96dc515c8efb40d49abd7d1477d13871b80e1ad4ba93b0. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 101)
      (PairLightPrepared19.rightRows.drop 101) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
