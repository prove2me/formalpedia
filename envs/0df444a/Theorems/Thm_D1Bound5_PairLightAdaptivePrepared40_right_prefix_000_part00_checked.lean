-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:32.466326+00:00
-- url     : https://prove2.me/theorems/2633ef2e-9c3a-434d-87ad-223ab5c85630
-- title:
--   Selected-floor prefix certificate for prepared pair 40, right list, part 0
-- statement:
--   For prepared pair 40, right list, part 0, the selected-floor certificate succeeds for at most `29` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 0 through 28; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight40_000Part00.lean, lines 7-11, SHA-256 01268829373f7fb667fe98c9cc18899867441a689cc07b11c6a5bd14a4c21387. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 29
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
