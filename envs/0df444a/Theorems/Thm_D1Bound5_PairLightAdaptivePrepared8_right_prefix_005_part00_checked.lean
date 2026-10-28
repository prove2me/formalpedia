-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:53:13.869984+00:00
-- url     : https://prove2.me/theorems/e6c8377a-917e-47bb-89f8-8adecda12c9e
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 0
-- statement:
--   For prepared pair 8, right list, part 0, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 375 through 394, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_005Part00.lean, lines 11-16, SHA-256 a140b40fd42a92ac5d9cb7f20877341db378b893b94e67fc1c296f1c8f054f3f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 20
      (PairLightPrepared8.rightCached.drop 375)
      (PairLightPrepared8.rightRows.drop 375) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
