-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:06.844983+00:00
-- url     : https://prove2.me/theorems/852f8c68-ff6f-4bac-a0cf-a9da0f135f92
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 5
-- statement:
--   For prepared pair 26, right list, part 5, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 15 through 17 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_000Part05.lean, lines 7-11, SHA-256 c1e6e834986c158b6e3f8befba48ebdd20b49cb371cc376a33b8ce1055c2559b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached000.drop 15) (rightRows000.drop 15) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
