-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:08.816498+00:00
-- url     : https://prove2.me/theorems/23c2efea-3b9f-479a-9e92-945b56037a13
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 6
-- statement:
--   For prepared pair 26, left list, part 6, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 250 through 250; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_003Part06.lean, lines 7-11, SHA-256 f18ca3e12ce27bb07bf00648145cdde72f8ae9b3b7a715ce831e778bf05e9df4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (leftCached003.drop 72) (leftRows003.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
