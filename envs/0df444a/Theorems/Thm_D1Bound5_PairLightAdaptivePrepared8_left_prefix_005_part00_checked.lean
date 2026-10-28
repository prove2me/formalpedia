-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:41.204534+00:00
-- url     : https://prove2.me/theorems/c00ad579-d205-4859-8618-119fdd7a03e5
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 0
-- statement:
--   For prepared pair 8, left list, part 0, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 376 through 395, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_005Part00.lean, lines 11-16, SHA-256 b2fc081e631b19da9fbf8f494882e50ce1b7d4712859e5447c92b7b478b21656. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 20
      (PairLightPrepared8.leftCached.drop 376)
      (PairLightPrepared8.leftRows.drop 376) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
