-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:01.287996+00:00
-- url     : https://prove2.me/theorems/fe8c887f-a1a0-4207-b500-cfd671b77aae
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 1
-- statement:
--   For prepared pair 6, left list, part 1, the selected-floor certificate succeeds for at most `46` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 506 through 551, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_005Part01.lean, lines 11-16, SHA-256 3afbc2e6db778bbec307c9a9b92b69405450683cf7460e57fe932325d54c0f9f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 46
      (PairLightPrepared6.leftCached.drop 506)
      (PairLightPrepared6.leftRows.drop 506) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
