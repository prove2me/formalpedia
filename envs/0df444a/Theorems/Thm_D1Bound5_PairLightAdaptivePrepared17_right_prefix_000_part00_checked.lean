-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:45.035573+00:00
-- url     : https://prove2.me/theorems/1261355e-c11b-4bc1-b40d-e77595dce9a4
-- title:
--   Selected-floor prefix certificate for prepared pair 17, right list, part 0
-- statement:
--   For prepared pair 17, right list, part 0, the selected-floor certificate succeeds for at most `29` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 0 through 28; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight17_000Part00.lean, lines 7-11, SHA-256 dacee6013036055f5f353f2a98513cb286f609968e681e7507f3b3f453419311. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 29
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
