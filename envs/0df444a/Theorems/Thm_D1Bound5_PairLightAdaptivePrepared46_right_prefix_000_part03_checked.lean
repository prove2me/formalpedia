-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:03.531985+00:00
-- url     : https://prove2.me/theorems/d14d285c-8c62-4255-ae1d-a30cbd75df53
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list, part 3
-- statement:
--   For prepared pair 46, right list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 58 through 81, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_000Part03.lean, lines 7-11, SHA-256 3dc9103ec363097c2fe02cb5a1f85911d309e448a057265666d5cbdc25ce21d4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 24
      (rightCached000.drop 58) (rightRows000.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
