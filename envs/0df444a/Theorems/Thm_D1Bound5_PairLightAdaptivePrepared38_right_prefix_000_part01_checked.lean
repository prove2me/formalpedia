-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:08.502253+00:00
-- url     : https://prove2.me/theorems/51541870-0a1b-49a3-ad3f-e17e7028a6b6
-- title:
--   Selected-floor prefix certificate for prepared pair 38, right list, part 1
-- statement:
--   For prepared pair 38, right list, part 1, the selected-floor certificate succeeds for at most `44` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared38.sieve`. Original heads 38 through 81; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight38_000Part01.lean, lines 7-11, SHA-256 bb22f9575e66c2de722bd1f1b6794d67f7679bfa888412e1b952df6a54e1fdb0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 44
      (rightCached000.drop 38) (rightRows000.drop 38) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared38
end
