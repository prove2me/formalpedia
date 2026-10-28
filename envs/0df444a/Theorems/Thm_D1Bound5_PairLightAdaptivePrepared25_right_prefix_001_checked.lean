-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:03.402465+00:00
-- url     : https://prove2.me/theorems/34a0e4c6-00be-4a87-9295-09439152ebfe
-- title:
--   Selected-floor prefix certificate for prepared pair 25, right list
-- statement:
--   For prepared pair 25, right list, the selected-floor certificate succeeds for at most `256` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Heads 125 through 380; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight25_001.lean, lines 12-36, SHA-256 df14893262f53c42ab87daef7a4f0d82708e6d76a109350414b163842ff5bb6d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 256
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
