-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:59.257394+00:00
-- url     : https://prove2.me/theorems/25270916-828f-4c7e-9643-287355a6c849
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list, part 2
-- statement:
--   For prepared pair 40, left list, part 2, the selected-floor certificate succeeds for at most `100` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 260 through 359; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_001Part02.lean, lines 7-11, SHA-256 5c36f5f47a3716027dbf60b8222068f07f43b4c9b900bba9f11bc9694a67cf97. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 100
      (leftCached001.drop 123) (leftRows001.drop 123) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
