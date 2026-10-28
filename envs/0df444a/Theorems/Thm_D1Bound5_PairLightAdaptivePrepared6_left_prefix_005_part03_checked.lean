-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:06.308196+00:00
-- url     : https://prove2.me/theorems/39d0f9e5-4095-4751-b08b-0559cce97ef7
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 3
-- statement:
--   For prepared pair 6, left list, part 3, the selected-floor certificate succeeds for at most `40` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 618 through 657, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_005Part03.lean, lines 11-16, SHA-256 67d9ee601c5d84a6692fece35eb1f89f882e83a59be32942db8962071cbc915c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 40
      (PairLightPrepared6.leftCached.drop 618)
      (PairLightPrepared6.leftRows.drop 618) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
