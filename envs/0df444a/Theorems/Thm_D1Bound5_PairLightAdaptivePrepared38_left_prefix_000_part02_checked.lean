-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:57.645858+00:00
-- url     : https://prove2.me/theorems/3e69dcaf-d5e8-490b-b416-2ef8d79c156a
-- title:
--   Selected-floor prefix certificate for prepared pair 38, left list, part 2
-- statement:
--   For prepared pair 38, left list, part 2, the selected-floor certificate succeeds for at most `58` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared38.sieve`. Original heads 82 through 139; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft38_000Part02.lean, lines 7-11, SHA-256 6e7004dbd140fe92b1ad68a47900d32f743da0cef3d51749e34cb6a2ee7056a2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 58
      (leftCached000.drop 82) (leftRows000.drop 82) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared38
end
