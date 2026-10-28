-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:25.575131+00:00
-- url     : https://prove2.me/theorems/98eb12a5-28d9-416a-b4e4-fc2400cc31da
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list, part 4
-- statement:
--   For prepared pair 40, left list, part 4, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 134 through 136; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_000Part04.lean, lines 7-11, SHA-256 0d4d43ba6b84ddfc3ba31549c34712bedc924a2eb9993d8e77538807749d14d9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 3
      (leftCached000.drop 134) (leftRows000.drop 134) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
