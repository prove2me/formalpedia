-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:53:12.138871+00:00
-- url     : https://prove2.me/theorems/fd0d9977-9dc1-40a7-9a9a-789ee674fbf3
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 4
-- statement:
--   For prepared pair 8, left list, part 4, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 246 through 259, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_003Part04.lean, lines 11-16, SHA-256 4c96c556861f7df7c51d86a5e1557b5c79db40794323d6e2383954ee80d9bb30. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.leftCached.drop 246)
      (PairLightPrepared8.leftRows.drop 246) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
