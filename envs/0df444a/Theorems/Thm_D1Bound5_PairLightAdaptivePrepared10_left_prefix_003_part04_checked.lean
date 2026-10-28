-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:19.157291+00:00
-- url     : https://prove2.me/theorems/73ca4338-67df-4630-a242-d332a6aaf9c3
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 4
-- statement:
--   For prepared pair 10, left list, part 4, the selected-floor certificate succeeds for at most `27` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 344 through 370, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_003Part04.lean, lines 11-16, SHA-256 095d315529dd8b4b011cd9218adb1f3f286d6d0cb795cbe3c135a44ece5b1676. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 27
      (PairLightPrepared10.leftCached.drop 344)
      (PairLightPrepared10.leftRows.drop 344) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
