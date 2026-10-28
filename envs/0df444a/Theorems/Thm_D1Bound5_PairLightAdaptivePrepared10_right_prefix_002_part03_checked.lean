-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:35.087624+00:00
-- url     : https://prove2.me/theorems/3c757566-76e6-494f-b129-de85ef4ea56a
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 3
-- statement:
--   For prepared pair 10, right list, part 3, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 201 through 217, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_002Part03.lean, lines 11-16, SHA-256 96d4e8a5671b9e6081b0587d5f4840aee944a7ed54c4628d49d0b09a614c9057. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 17
      (PairLightPrepared10.rightCached.drop 201)
      (PairLightPrepared10.rightRows.drop 201) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
