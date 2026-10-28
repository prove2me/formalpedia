-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_004_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_004_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:39.416978+00:00
-- url     : https://prove2.me/theorems/370c6a09-d77c-40f5-b4c3-29b565327abc
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 2
-- statement:
--   For prepared pair 4, right list, part 2, the selected-floor certificate succeeds for at most `64` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 486 through 549, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_004Part02.lean, lines 11-16, SHA-256 c0ab3699107d0ce8c813eadf9124d1446eb48f77f3d3062b2e09d2b5e05800cc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_004_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 64
      (PairLightPrepared4.rightCached.drop 486)
      (PairLightPrepared4.rightRows.drop 486) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
