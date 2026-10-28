-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:01.456868+00:00
-- url     : https://prove2.me/theorems/1e30f50a-23ce-46e7-8636-3d246f75bb65
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 6
-- statement:
--   For prepared pair 4, right list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 402 through 404, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_003Part06.lean, lines 11-16, SHA-256 5ec93387c3158aff56730e335d2a48f2663808e3b690fd5c17956c2cfd8795d9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 3
      (PairLightPrepared4.rightCached.drop 402)
      (PairLightPrepared4.rightRows.drop 402) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
