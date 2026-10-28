-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:30.300934+00:00
-- url     : https://prove2.me/theorems/e6f98888-dccf-4d43-b391-cc0c44671699
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 2
-- statement:
--   For prepared pair 4, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 22 through 33, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_000Part02.lean, lines 11-16, SHA-256 007e488ed48aef50b02d7b52a0db4b44f03e94a1870c1b5b7cf6201dddbffc7d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 12
      (PairLightPrepared4.rightCached.drop 22)
      (PairLightPrepared4.rightRows.drop 22) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
