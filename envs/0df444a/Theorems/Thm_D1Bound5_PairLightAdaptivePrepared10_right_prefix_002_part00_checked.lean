-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:23.755175+00:00
-- url     : https://prove2.me/theorems/058cc78c-129b-48cf-abaf-6addb03c3577
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 0
-- statement:
--   For prepared pair 10, right list, part 0, the selected-floor certificate succeeds for at most `15` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 153 through 167, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_002Part00.lean, lines 11-16, SHA-256 f8cc9dcb4d18d96204df5ff367b42f5ce0af80f5ad5f400f549baa7746c474ce. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 15
      (PairLightPrepared10.rightCached.drop 153)
      (PairLightPrepared10.rightRows.drop 153) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
