-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:34.208033+00:00
-- url     : https://prove2.me/theorems/eefac2ca-8b48-4992-abac-c7df59e8f1fe
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 5
-- statement:
--   For prepared pair 24, right list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 221 through 244, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_001Part05.lean, lines 11-16, SHA-256 12e4b18d280bc0d9c5e05d9e8027c5cdd8971cfcd1b0cadda90003fb552d0d62. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.rightCached.drop 221)
      (PairLightPrepared24.rightRows.drop 221) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
