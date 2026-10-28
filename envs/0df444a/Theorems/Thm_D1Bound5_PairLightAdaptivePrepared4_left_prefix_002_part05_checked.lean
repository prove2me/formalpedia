-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:08.410688+00:00
-- url     : https://prove2.me/theorems/d311ffc5-4bcb-4bb4-ba38-7fb3cd7701bd
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 5
-- statement:
--   For prepared pair 4, left list, part 5, the selected-floor certificate succeeds for at most `19` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 236 through 254, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_002Part05.lean, lines 11-16, SHA-256 55cf04529a75e893f832fefbb986f7f390c206b2ab08fa9c25d4d2a85db48b03. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 19
      (PairLightPrepared4.leftCached.drop 236)
      (PairLightPrepared4.leftRows.drop 236) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
