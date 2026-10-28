-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_004_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:30.516223+00:00
-- url     : https://prove2.me/theorems/f0855557-7697-4b71-a46c-675da19dc28e
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 1
-- statement:
--   For prepared pair 10, left list, part 1, the selected-floor certificate succeeds for at most `45` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 441 through 485, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_004Part01.lean, lines 11-16, SHA-256 bab6f793e8716cde005e4d63b11bb8d64fa773737bb847a9e7ff7c4a15052fef. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 45
      (PairLightPrepared10.leftCached.drop 441)
      (PairLightPrepared10.leftRows.drop 441) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
