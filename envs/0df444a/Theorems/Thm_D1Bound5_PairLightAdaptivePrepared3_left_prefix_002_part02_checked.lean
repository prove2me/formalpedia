-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:33.688562+00:00
-- url     : https://prove2.me/theorems/996bea7a-5e16-4b5a-aa79-102964ef4886
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 2
-- statement:
--   For prepared pair 3, left list, part 2, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 359 through 382, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_002Part02.lean, lines 9-14, SHA-256 c22dfdfcd2b8ab638406e47f9578164c9bb4d76815ede4b25ade0cdb67bf7e9e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.leftCached.drop 359)
      (PairLightPrepared3.leftRows.drop 359) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
