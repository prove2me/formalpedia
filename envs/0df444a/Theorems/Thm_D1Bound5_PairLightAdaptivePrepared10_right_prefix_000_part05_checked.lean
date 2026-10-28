-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:58.682182+00:00
-- url     : https://prove2.me/theorems/c81877dc-7687-42d9-bcaf-5165a53c41c0
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 5
-- statement:
--   For prepared pair 10, right list, part 5, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 58 through 70, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_000Part05.lean, lines 11-16, SHA-256 e911b646a04f518f87ed18be2ba2602b6daa54e3a23edc6e25e7c93760d2170a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 13
      (PairLightPrepared10.rightCached.drop 58)
      (PairLightPrepared10.rightRows.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
