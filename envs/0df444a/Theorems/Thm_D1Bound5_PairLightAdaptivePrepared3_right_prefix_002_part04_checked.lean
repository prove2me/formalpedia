-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.right_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:43.35767+00:00
-- url     : https://prove2.me/theorems/c6ebae92-662b-4735-a69c-a57049d330d0
-- title:
--   Selected-floor prefix certificate for prepared pair 3, right list, part 4
-- statement:
--   For prepared pair 3, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 402 through 413, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight3_002Part04.lean, lines 10-15, SHA-256 761ffb3a869016c5ecffd5d6d5b5ffacd1accc081e7770e70de08c9bfa76c684. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.right_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 12
      (PairLightPrepared3.rightCached.drop 402)
      (PairLightPrepared3.rightRows.drop 402) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
