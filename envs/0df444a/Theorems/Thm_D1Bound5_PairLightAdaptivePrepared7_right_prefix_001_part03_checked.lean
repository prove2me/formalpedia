-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:10.762068+00:00
-- url     : https://prove2.me/theorems/85478479-1773-420f-867d-53ed2251de97
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 3
-- statement:
--   For prepared pair 7, right list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 178 through 201, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_001Part03.lean, lines 11-16, SHA-256 fe1f7eaf3bc2bdf8fe835ab4e3dd26ff16528ca8a85f7f9f176579ccbfc57a3a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.rightCached.drop 178)
      (PairLightPrepared7.rightRows.drop 178) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
