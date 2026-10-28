-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:11.831719+00:00
-- url     : https://prove2.me/theorems/e9db1e96-8ea1-4d75-98f2-8537c5fce0ea
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 2
-- statement:
--   For prepared pair 6, left list, part 2, the selected-floor certificate succeeds for at most `66` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 552 through 617, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_005Part02.lean, lines 11-16, SHA-256 f261436074dca3476c5434937bcfee8f3e06b7e6784b751d7a25854c121da14e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 66
      (PairLightPrepared6.leftCached.drop 552)
      (PairLightPrepared6.leftRows.drop 552) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
