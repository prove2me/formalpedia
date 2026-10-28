-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:58.310927+00:00
-- url     : https://prove2.me/theorems/e7fcbdab-9a92-44bc-8854-333a90a82627
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 1
-- statement:
--   For prepared pair 8, left list, part 1, the selected-floor certificate succeeds for at most `21` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 396 through 416, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_005Part01.lean, lines 11-16, SHA-256 79845d4821166036aeb1dad95f45a4944e20c9c10de755a88a2e5b3f9dd3eee2. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 21
      (PairLightPrepared8.leftCached.drop 396)
      (PairLightPrepared8.leftRows.drop 396) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
