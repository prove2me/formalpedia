-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:01.581102+00:00
-- url     : https://prove2.me/theorems/e8472b6c-4a96-4bf2-abb2-a6b9d36a6f90
-- title:
--   Selected-floor prefix certificate for prepared pair 18, left list, part 3
-- statement:
--   For prepared pair 18, left list, part 3, the selected-floor certificate succeeds for at most `131` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared18.sieve`. Original heads 131 through 261; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft18_000Part03.lean, lines 7-11, SHA-256 bf1ad8800a4c12e613156fcec41903be9be9fdeaf9480a0999e4635a369f1b47. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 131
      (leftCached000.drop 131) (leftRows000.drop 131) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared18
end
