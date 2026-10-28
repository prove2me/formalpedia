-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:22.512955+00:00
-- url     : https://prove2.me/theorems/ceff1ce2-cc8e-405f-83f4-281413a77537
-- title:
--   Selected-floor prefix certificate for prepared pair 25, left list
-- statement:
--   For prepared pair 25, left list, the selected-floor certificate succeeds for at most `126` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft25_000.lean, lines 13-42, SHA-256 4828a671e2e362b50625b746fc4bd37541a0b650c9b3b5ff181f44194f72cb23. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 126
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
