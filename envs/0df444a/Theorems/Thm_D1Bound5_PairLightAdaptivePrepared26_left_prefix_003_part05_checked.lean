-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:41.499963+00:00
-- url     : https://prove2.me/theorems/4222231f-60a1-434c-8b22-7f3c2f413a24
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 5
-- statement:
--   For prepared pair 26, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 238 through 249; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_003Part05.lean, lines 7-11, SHA-256 295ce75bf10818fea30c93779b68e719c9bbf638204470a6b3ae4f0a38055bb5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached003.drop 60) (leftRows003.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
