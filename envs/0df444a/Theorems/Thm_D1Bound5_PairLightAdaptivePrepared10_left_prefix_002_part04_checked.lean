-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:51.294513+00:00
-- url     : https://prove2.me/theorems/8bbecc57-9cd6-490f-9494-221c6e98a3ac
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 4
-- statement:
--   For prepared pair 10, left list, part 4, the selected-floor certificate succeeds for at most `18` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 218 through 235, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_002Part04.lean, lines 11-16, SHA-256 b1428a115cbce055a39e67e7f3b727aba0097672ed2280588cafb8181bcfa03c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 18
      (PairLightPrepared10.leftCached.drop 218)
      (PairLightPrepared10.leftRows.drop 218) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
