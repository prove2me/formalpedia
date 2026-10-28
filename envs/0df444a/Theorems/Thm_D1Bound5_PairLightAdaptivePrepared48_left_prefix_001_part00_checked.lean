-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:36.460265+00:00
-- url     : https://prove2.me/theorems/3e96937c-09b9-4399-bbeb-03f4a1127971
-- title:
--   Selected-floor prefix certificate for prepared pair 48, left list, part 0
-- statement:
--   For prepared pair 48, left list, part 0, the selected-floor certificate succeeds for at most `50` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 137 through 186; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft48_001Part00.lean, lines 7-11, SHA-256 2d10512315c9c600aee8fc4ceeed44e71b6f2c4389cd27be6a166a7c86d7043b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 50
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
