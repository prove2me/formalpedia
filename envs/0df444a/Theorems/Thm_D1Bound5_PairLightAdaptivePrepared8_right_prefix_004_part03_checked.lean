-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:00.787958+00:00
-- url     : https://prove2.me/theorems/8da2f287-01dc-44d8-8f52-2c5862095e03
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 3
-- statement:
--   For prepared pair 8, right list, part 3, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 321 through 337, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_004Part03.lean, lines 11-16, SHA-256 4faa7077930f6e9b309188418a1e8feba3fe79f08ca56154abd9035c3519edaf. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 17
      (PairLightPrepared8.rightCached.drop 321)
      (PairLightPrepared8.rightRows.drop 321) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
