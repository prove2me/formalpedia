-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_003_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_003_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:42.642136+00:00
-- url     : https://prove2.me/theorems/0bd4a336-e555-481f-baa2-ab8b517976ad
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 3
-- statement:
--   For prepared pair 8, right list, part 3, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 232 through 245, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_003Part03.lean, lines 11-16, SHA-256 8d36b560e77bf7ffee9e5f5e86e351dd5d10e4380e41969e24a3dfd01b052e24. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_003_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.rightCached.drop 232)
      (PairLightPrepared8.rightRows.drop 232) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
