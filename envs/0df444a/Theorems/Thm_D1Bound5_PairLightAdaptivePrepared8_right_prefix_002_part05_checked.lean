-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:26.914186+00:00
-- url     : https://prove2.me/theorems/dda35f96-5eb9-4665-a7ec-aaf7368b5c7c
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 5
-- statement:
--   For prepared pair 8, right list, part 5, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 179 through 191, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_002Part05.lean, lines 11-16, SHA-256 069292d6f8600e4daf3fb8a486b28c6aa9ba959ba65dcce5cf5722dcd5603db2. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 13
      (PairLightPrepared8.rightCached.drop 179)
      (PairLightPrepared8.rightRows.drop 179) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
