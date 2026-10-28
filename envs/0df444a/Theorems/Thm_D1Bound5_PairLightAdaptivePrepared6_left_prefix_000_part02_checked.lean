-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:03.073113+00:00
-- url     : https://prove2.me/theorems/243e3323-2bc3-4f89-b73b-0e259708d562
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 2
-- statement:
--   For prepared pair 6, left list, part 2, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 20 through 29, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_000Part02.lean, lines 11-16, SHA-256 024b84575740c11726833743fb885e6cdfa8c1a681ebc2b8fb18cce5aad51ebb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 10
      (PairLightPrepared6.leftCached.drop 20)
      (PairLightPrepared6.leftRows.drop 20) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
