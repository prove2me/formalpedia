-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:54.083522+00:00
-- url     : https://prove2.me/theorems/2683aced-c39d-4874-a900-588be4ae424a
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 6
-- statement:
--   For prepared pair 6, right list, part 6, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 320 through 320, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_003Part06.lean, lines 11-16, SHA-256 64a44000372e15363038ed796e93ae67b35427ca9cc81faf5040f8c2cdf042da. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 1
      (PairLightPrepared6.rightCached.drop 320)
      (PairLightPrepared6.rightRows.drop 320) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
