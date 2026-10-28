-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_006_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:38.071819+00:00
-- url     : https://prove2.me/theorems/b90aa951-8f62-4865-8751-de34504a4c95
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 9
-- statement:
--   For prepared pair 26, left list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 551 through 562; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_006Part09.lean, lines 7-11, SHA-256 845fed2fca8f2b00fa09655526154d046548793eb60d4f6f738146f6fe4d81a6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part09_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached006.drop 108) (leftRows006.drop 108) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
