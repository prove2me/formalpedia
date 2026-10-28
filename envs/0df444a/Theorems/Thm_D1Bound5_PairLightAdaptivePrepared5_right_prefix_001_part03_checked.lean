-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:00.260464+00:00
-- url     : https://prove2.me/theorems/0f46ff74-67d9-4fdc-a32f-6793410de64c
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 3
-- statement:
--   For prepared pair 5, right list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 178 through 201, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_001Part03.lean, lines 11-16, SHA-256 5cbf621247c551d8065f1c2173051e6f636bd648dc4f7c6adcf85845925e3071. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.rightCached.drop 178)
      (PairLightPrepared5.rightRows.drop 178) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
