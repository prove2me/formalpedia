-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:41.438106+00:00
-- url     : https://prove2.me/theorems/75332743-0929-4734-9366-71236143903e
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 9
-- statement:
--   For prepared pair 3, left list, part 9, the selected-floor certificate succeeds for at most `4` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 108 through 111, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_000Part09.lean, lines 9-14, SHA-256 674b45d454274b77139ee2e5e59b9d12529a75b94d95a8c628b2258d0bbbe30e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part09_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 4
      (PairLightPrepared3.leftCached.drop 108)
      (PairLightPrepared3.leftRows.drop 108) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
