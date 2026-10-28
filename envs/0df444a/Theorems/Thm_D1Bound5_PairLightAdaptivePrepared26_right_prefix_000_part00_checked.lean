-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:01.459292+00:00
-- url     : https://prove2.me/theorems/fff7eecb-851c-4b45-b3e8-8b942757dc27
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 0
-- statement:
--   For prepared pair 26, right list, part 0, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 0 through 2 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_000Part00.lean, lines 7-11, SHA-256 be81b69bc07c22d42b965e1916ebba20298d4ea2a9ac9a341209ba0213cc5d0e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
