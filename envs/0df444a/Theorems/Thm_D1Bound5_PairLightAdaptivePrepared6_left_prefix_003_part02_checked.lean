-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_003_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_003_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:30.195045+00:00
-- url     : https://prove2.me/theorems/e709efec-7686-4fd6-8d58-b58984291705
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 2
-- statement:
--   For prepared pair 6, left list, part 2, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 247 through 263, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_003Part02.lean, lines 11-16, SHA-256 4de80b50e7da47648cefd71c437e0abd37037aff03eaffd059d49199069b720a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_003_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 17
      (PairLightPrepared6.leftCached.drop 247)
      (PairLightPrepared6.leftRows.drop 247) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
