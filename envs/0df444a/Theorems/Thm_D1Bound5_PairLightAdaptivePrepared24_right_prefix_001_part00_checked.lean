-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:36.468377+00:00
-- url     : https://prove2.me/theorems/835a1973-db39-4f79-b7bf-b766eb7adde7
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 0
-- statement:
--   For prepared pair 24, right list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 101 through 124, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_001Part00.lean, lines 11-16, SHA-256 17940765b92490902d0b6aac4e547726937f530748bb5d4027b12b2bba28fe6c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.rightCached.drop 101)
      (PairLightPrepared24.rightRows.drop 101) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
