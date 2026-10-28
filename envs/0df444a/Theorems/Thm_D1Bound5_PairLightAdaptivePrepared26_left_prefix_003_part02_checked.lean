-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_003_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:47.767162+00:00
-- url     : https://prove2.me/theorems/2ea1fede-1a0d-4815-b30c-dff48b1d6163
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 2
-- statement:
--   For prepared pair 26, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 202 through 213; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_003Part02.lean, lines 7-11, SHA-256 773fce57e9a906ee6cd28ca8649cfd78ee5ce0062925fb35e48e6bde275c870c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached003.drop 24) (leftRows003.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
