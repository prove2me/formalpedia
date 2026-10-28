-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_006_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:03.567582+00:00
-- url     : https://prove2.me/theorems/1f0a1252-2116-4fc3-a0de-f5120a9ae1b2
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 6
-- statement:
--   For prepared pair 26, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 515 through 526; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_006Part06.lean, lines 7-11, SHA-256 0dec060f019103f25fb2c2449b67d50804188af83f715526f6adc08e8d126164. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached006.drop 72) (leftRows006.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
