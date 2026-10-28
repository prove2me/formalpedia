-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_006_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_006_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:12.786973+00:00
-- url     : https://prove2.me/theorems/7102f3d6-a3c4-4621-bf96-78bbb91d66cf
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 3
-- statement:
--   For prepared pair 8, left list, part 3, the selected-floor certificate succeeds for at most `40` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 676 through 715, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_006Part03.lean, lines 11-16, SHA-256 315defb5ff57d045dc895c084a6c78bdeee45260d3b338f3aa0c21d23a62122f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_006_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 40
      (PairLightPrepared8.leftCached.drop 676)
      (PairLightPrepared8.leftRows.drop 676) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
