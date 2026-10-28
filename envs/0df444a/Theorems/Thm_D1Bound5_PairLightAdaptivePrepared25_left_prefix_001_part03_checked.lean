-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:55.641375+00:00
-- url     : https://prove2.me/theorems/35b50aaf-061a-498b-98cc-914fd7cf4594
-- title:
--   Selected-floor prefix certificate for prepared pair 25, left list, part 3
-- statement:
--   For prepared pair 25, left list, part 3, the selected-floor certificate succeeds for at most `105` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 275 through 379, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft25_001Part03.lean, lines 7-11, SHA-256 e3b2f95178ef4b74b75415db35f2318e1ff81afc000e639fc4fdbe8244839bab. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 105
      (leftCached001.drop 149) (leftRows001.drop 149) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
