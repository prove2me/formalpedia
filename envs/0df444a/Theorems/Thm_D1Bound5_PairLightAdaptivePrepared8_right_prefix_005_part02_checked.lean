-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:14.269528+00:00
-- url     : https://prove2.me/theorems/6c1afdf4-0b54-4fa3-8a2d-0553f50a0da2
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 2
-- statement:
--   For prepared pair 8, right list, part 2, the selected-floor certificate succeeds for at most `23` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 416 through 438, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_005Part02.lean, lines 11-16, SHA-256 d4dac12e679db7479b0611b746b17b0de4653d75047be6f5875f252460b45c84. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 23
      (PairLightPrepared8.rightCached.drop 416)
      (PairLightPrepared8.rightRows.drop 416) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
