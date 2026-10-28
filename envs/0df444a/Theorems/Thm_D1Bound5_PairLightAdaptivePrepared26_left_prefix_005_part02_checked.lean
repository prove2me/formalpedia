-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_005_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:21.962683+00:00
-- url     : https://prove2.me/theorems/b1952380-89fa-4a3e-890f-793cad850c7d
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 2
-- statement:
--   For prepared pair 26, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 360 through 371; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_005Part02.lean, lines 7-11, SHA-256 96e4e552e2b2697765b07fed09796f29c0c9bc81f2f3852f65f577e8f5bc5e3d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached005.drop 24) (leftRows005.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
