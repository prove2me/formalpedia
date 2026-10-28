-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_003_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:38.188684+00:00
-- url     : https://prove2.me/theorems/168cbbb5-59d5-4d23-a4dd-12e4d851b56c
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 3
-- statement:
--   For prepared pair 4, right list, part 3, the selected-floor certificate succeeds for at most `25` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 319 through 343, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_003Part03.lean, lines 11-16, SHA-256 497f477ccfbf4744742ae8c25358c6fbed55f046ed1888b68d4b1bbf9a73f0ef. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 25
      (PairLightPrepared4.rightCached.drop 319)
      (PairLightPrepared4.rightRows.drop 319) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
