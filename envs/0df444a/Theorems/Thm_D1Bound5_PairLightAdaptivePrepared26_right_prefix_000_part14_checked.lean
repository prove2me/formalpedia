-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_000_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:02.162877+00:00
-- url     : https://prove2.me/theorems/554d3e40-d9f9-42c7-8c17-7d3f55ed47bf
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 14
-- statement:
--   For prepared pair 26, right list, part 14, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 42 through 44 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_000Part14.lean, lines 7-11, SHA-256 a582ed2e9f5dd6de9830fd26eb0c773a13a9227f8702bfd18352f1720efa70ed. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part14_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached000.drop 42) (rightRows000.drop 42) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
