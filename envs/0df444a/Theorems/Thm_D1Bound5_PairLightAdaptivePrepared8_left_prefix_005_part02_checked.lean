-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:53.220095+00:00
-- url     : https://prove2.me/theorems/621d0a23-f237-497b-90c1-52ed0d18ce79
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 2
-- statement:
--   For prepared pair 8, left list, part 2, the selected-floor certificate succeeds for at most `23` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 417 through 439, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_005Part02.lean, lines 11-16, SHA-256 af73938c952e333170a6898e16c26a30d840ce039ea214bcbf7f0168a08afddb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 23
      (PairLightPrepared8.leftCached.drop 417)
      (PairLightPrepared8.leftRows.drop 417) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
