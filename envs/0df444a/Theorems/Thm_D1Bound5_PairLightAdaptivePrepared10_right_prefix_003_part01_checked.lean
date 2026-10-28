-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_003_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:42.313759+00:00
-- url     : https://prove2.me/theorems/57c3b251-92a4-4e81-9c3f-11eb6a2659f2
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 1
-- statement:
--   For prepared pair 10, right list, part 1, the selected-floor certificate succeeds for at most `21` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 275 through 295, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_003Part01.lean, lines 11-16, SHA-256 cb4bc3dcb2f4dc86f329c25fbef7e8ac289ddd3211bcd8818a155c74e54e80e7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 21
      (PairLightPrepared10.rightCached.drop 275)
      (PairLightPrepared10.rightRows.drop 275) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
