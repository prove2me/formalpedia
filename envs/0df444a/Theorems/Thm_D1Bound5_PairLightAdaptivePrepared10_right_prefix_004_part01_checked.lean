-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_004_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_004_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:51:23.959605+00:00
-- url     : https://prove2.me/theorems/61ecf1b2-3861-44f8-b60f-f07cab8f051c
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 1
-- statement:
--   For prepared pair 10, right list, part 1, the selected-floor certificate succeeds for at most `45` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 441 through 485, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_004Part01.lean, lines 11-16, SHA-256 7785f19529a3b0b20d63e62a633011c409bd7ab0e918bf5a4939bfd1970614ef. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_004_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 45
      (PairLightPrepared10.rightCached.drop 441)
      (PairLightPrepared10.rightRows.drop 441) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
