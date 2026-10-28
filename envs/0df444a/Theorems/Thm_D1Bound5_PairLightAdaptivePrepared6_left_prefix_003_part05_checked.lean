-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:11.900308+00:00
-- url     : https://prove2.me/theorems/9c6d4f5a-6f00-443a-a506-526ddbfcd306
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 5
-- statement:
--   For prepared pair 6, left list, part 5, the selected-floor certificate succeeds for at most `19` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 299 through 317, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_003Part05.lean, lines 11-16, SHA-256 d0c2a83e2c361a360616fcedc69a30cee5e7725b5a2e9e7ec5605d80cc57c710. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_003_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 19
      (PairLightPrepared6.leftCached.drop 299)
      (PairLightPrepared6.leftRows.drop 299) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
