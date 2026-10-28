-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:39.737979+00:00
-- url     : https://prove2.me/theorems/2dffc2ae-5e6a-4c03-bf01-b930186a12d4
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 3
-- statement:
--   For prepared pair 4, right list, part 3, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 201 through 217, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_002Part03.lean, lines 11-16, SHA-256 d83616cf44c752ca9ff9ed793a0ffaceb1c2d03521d8a2b1d2b9a014231ce245. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 17
      (PairLightPrepared4.rightCached.drop 201)
      (PairLightPrepared4.rightRows.drop 201) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
