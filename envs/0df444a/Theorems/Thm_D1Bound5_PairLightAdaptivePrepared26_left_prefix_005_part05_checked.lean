-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_005_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:55.648245+00:00
-- url     : https://prove2.me/theorems/6f11d20a-39e2-4556-b825-9a6856febbe0
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 5
-- statement:
--   For prepared pair 26, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 396 through 407; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_005Part05.lean, lines 7-11, SHA-256 8fdf0d5a8b9abff427bab30d514571032e51db4de8d334e13f3b59a6bc9c10b6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached005.drop 60) (leftRows005.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
