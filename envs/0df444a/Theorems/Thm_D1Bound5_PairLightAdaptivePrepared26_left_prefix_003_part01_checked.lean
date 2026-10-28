-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_003_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:40.437994+00:00
-- url     : https://prove2.me/theorems/66d986b9-a132-4c72-8cbb-83358a4fc4a1
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 1
-- statement:
--   For prepared pair 26, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 190 through 201; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_003Part01.lean, lines 7-11, SHA-256 0f23a7dbcd1ea6ef10526360a7362daa10e18dc597170792991dae5f45d80509. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached003.drop 12) (leftRows003.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
