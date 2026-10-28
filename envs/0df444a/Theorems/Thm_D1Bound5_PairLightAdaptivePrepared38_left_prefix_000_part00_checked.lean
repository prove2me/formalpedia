-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:36.03858+00:00
-- url     : https://prove2.me/theorems/8431e8c7-278b-40bd-9e95-52f0a8ad4192
-- title:
--   Selected-floor prefix certificate for prepared pair 38, left list, part 0
-- statement:
--   For prepared pair 38, left list, part 0, the selected-floor certificate succeeds for at most `37` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared38.sieve`. Original heads 0 through 36; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft38_000Part00.lean, lines 7-11, SHA-256 620421bd52b7197380fa6423e2f0b18d06f58f84de2ff33df7a3980fb94cba04. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 37
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared38
end
