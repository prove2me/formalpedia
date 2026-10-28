-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:43.633274+00:00
-- url     : https://prove2.me/theorems/ce3cb74c-20eb-4d7e-ba51-c58218ca3a24
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 0
-- statement:
--   For prepared pair 3, left list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 311 through 334, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_002Part00.lean, lines 9-14, SHA-256 a6a9d9281b5982792b73b3a37f2acd1c5f15d17bcba53a0810e94dce2d56e5cc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.leftCached.drop 311)
      (PairLightPrepared3.leftRows.drop 311) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
