-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_003_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:01.56248+00:00
-- url     : https://prove2.me/theorems/8bdede41-4547-433a-b757-bb0d0be89aad
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 0
-- statement:
--   For prepared pair 26, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads178 through189; every head keeps its entire later-vertex tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_003Part00.lean, lines 7-11, SHA-256 b154dd8f7a9e14aaac46cec6b138c9414b8e3d97d00128b1960057821be64c50. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached003.drop 0) (leftRows003.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
