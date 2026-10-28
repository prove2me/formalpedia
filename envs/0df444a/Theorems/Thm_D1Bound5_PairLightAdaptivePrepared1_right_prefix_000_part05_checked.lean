-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:42.208664+00:00
-- url     : https://prove2.me/theorems/918c83d6-2a78-491b-878f-e0247b074119
-- title:
--   Selected-floor prefix certificate for prepared pair 1, right list, part 5
-- statement:
--   For prepared pair 1, right list, part 5, the selected-floor certificate succeeds for at most `30` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 108 through 137, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight1_000Part05.lean, lines 7-11, SHA-256 a7b4c5d1e5539069cb33121bb6e5b1797586c144ba08f077a723d68eaa57b2d2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 30
      (rightCached000.drop 108) (rightRows000.drop 108) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
