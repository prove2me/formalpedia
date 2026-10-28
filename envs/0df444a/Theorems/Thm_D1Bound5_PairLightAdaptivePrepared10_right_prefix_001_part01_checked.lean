-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:56.352759+00:00
-- url     : https://prove2.me/theorems/0762e373-749c-4b04-b379-627ee77813d5
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 1
-- statement:
--   For prepared pair 10, right list, part 1, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 84 through 96, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_001Part01.lean, lines 11-16, SHA-256 169973f4548731debb0c438eaac42b7543c492ec927592879379e87f3260f33c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 13
      (PairLightPrepared10.rightCached.drop 84)
      (PairLightPrepared10.rightRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
