-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:49.515001+00:00
-- url     : https://prove2.me/theorems/b38696d5-758c-4427-81ab-e8c17367d156
-- title:
--   Selected-floor prefix certificate for prepared pair 25, right list, part 3
-- statement:
--   For prepared pair 25, right list, part 3, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 78 through 108, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight25_000Part03.lean, lines 7-11, SHA-256 f20c55942f981867687c446ead5dbd676162e97d5ab4d82128ecbfd599b6cc43. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 31
      (rightCached000.drop 78) (rightRows000.drop 78) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
