-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_003_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:17.274769+00:00
-- url     : https://prove2.me/theorems/24bf2aa9-4060-44a7-9348-adc499845792
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 3
-- statement:
--   For prepared pair 10, right list, part 3, the selected-floor certificate succeeds for at most `25` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 319 through 343, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_003Part03.lean, lines 11-16, SHA-256 85aa3d958ec9328a5a35e85eadd24e6426fd2b2a31f0dfb732cc88473c846941. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 25
      (PairLightPrepared10.rightCached.drop 319)
      (PairLightPrepared10.rightRows.drop 319) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
