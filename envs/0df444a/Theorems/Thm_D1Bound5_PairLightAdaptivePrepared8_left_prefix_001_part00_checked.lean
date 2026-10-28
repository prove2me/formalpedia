-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:25.235773+00:00
-- url     : https://prove2.me/theorems/7f22ca83-43d0-4e05-a2b3-2de204ce58b3
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 0
-- statement:
--   For prepared pair 8, left list, part 0, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 58 through 67, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_001Part00.lean, lines 11-16, SHA-256 13d8ce5c95d69b6e5d52a45e852aa603f915d74e194cf00e988e07c91e5d2471. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 10
      (PairLightPrepared8.leftCached.drop 58)
      (PairLightPrepared8.leftRows.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
