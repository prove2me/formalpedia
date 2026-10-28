-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:49.133623+00:00
-- url     : https://prove2.me/theorems/e80e30e3-ae50-4b1c-ac51-04f851fdc24a
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 3
-- statement:
--   For prepared pair 7, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 36 through 47, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_000Part03.lean, lines 11-16, SHA-256 ff5bded5cda512053f7707669c7848672794fd78aa1663cf0dcec5d04826336c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.rightCached.drop 36)
      (PairLightPrepared7.rightRows.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
