-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_006_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_006_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:10.526994+00:00
-- url     : https://prove2.me/theorems/ebed39c5-c25c-4140-9b2d-918e1619dc5d
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 2
-- statement:
--   For prepared pair 8, left list, part 2, the selected-floor certificate succeeds for at most `66` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 610 through 675, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_006Part02.lean, lines 11-16, SHA-256 aa2ddf89f8acc5329a68864ed9a69573bdc7af5a663d6c3d2bb20e8eedebaedd. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_006_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 66
      (PairLightPrepared8.leftCached.drop 610)
      (PairLightPrepared8.leftRows.drop 610) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
