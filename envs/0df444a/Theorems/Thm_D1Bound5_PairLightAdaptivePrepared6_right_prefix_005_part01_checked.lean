-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_005_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_005_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:52.022434+00:00
-- url     : https://prove2.me/theorems/e3f1a71f-c743-4df5-a78e-7a8b04790cc0
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 1
-- statement:
--   For prepared pair 6, right list, part 1, the selected-floor certificate succeeds for at most `49` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 514 through 562, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_005Part01.lean, lines 11-16, SHA-256 5ac9fe7a2e2819b6c3e59a3ffa7744af555d8a33358160fd6f44018ed530b4e9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_005_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 49
      (PairLightPrepared6.rightCached.drop 514)
      (PairLightPrepared6.rightRows.drop 514) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
