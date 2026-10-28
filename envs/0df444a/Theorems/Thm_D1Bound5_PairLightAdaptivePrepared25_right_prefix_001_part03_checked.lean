-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:36.758254+00:00
-- url     : https://prove2.me/theorems/64ea30a3-02b3-4c42-9a2b-263e40977872
-- title:
--   Selected-floor prefix certificate for prepared pair 25, right list, part 3
-- statement:
--   For prepared pair 25, right list, part 3, the selected-floor certificate succeeds for at most `108` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 273 through 380, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight25_001Part03.lean, lines 7-11, SHA-256 7a21832be6b1034ffd1b65dd5a0b5c5b461a3f6d1c5f30d7d996e6d9416c6d5e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 108
      (rightCached001.drop 148) (rightRows001.drop 148) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
