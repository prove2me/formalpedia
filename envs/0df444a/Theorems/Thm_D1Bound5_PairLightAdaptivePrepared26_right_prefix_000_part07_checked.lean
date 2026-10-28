-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:05.656262+00:00
-- url     : https://prove2.me/theorems/3c5e6df6-7c20-491f-91c7-937ccbfa4453
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 7
-- statement:
--   For prepared pair 26, right list, part 7, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 21 through 23 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_000Part07.lean, lines 7-11, SHA-256 c79c08e753988172041fd997655cb5d5ad6143e22d860d272222c21c6104ce4c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached000.drop 21) (rightRows000.drop 21) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
