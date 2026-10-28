-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:21.799987+00:00
-- url     : https://prove2.me/theorems/2fbec0c6-570d-4631-bd36-d5d7240b7e95
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 2
-- statement:
--   For prepared pair 10, left list, part 2, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 184 through 200, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_002Part02.lean, lines 11-16, SHA-256 dd1a519fe5b7e177226889ef7d9a43cd8a5cb935bd0158ea1a675b925dc6d6b9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 17
      (PairLightPrepared10.leftCached.drop 184)
      (PairLightPrepared10.leftRows.drop 184) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
