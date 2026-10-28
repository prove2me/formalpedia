-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:19.797776+00:00
-- url     : https://prove2.me/theorems/e8aac205-7d4a-42a0-85c2-928809ae3440
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 5
-- statement:
--   For prepared pair 8, right list, part 5, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 48 through 57, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_000Part05.lean, lines 11-16, SHA-256 3f1fa1fef6259b6a251e48ac1b5057077813143814f68abf35750cb5f3b85101. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 10
      (PairLightPrepared8.rightCached.drop 48)
      (PairLightPrepared8.rightRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
