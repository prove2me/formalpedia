-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:57.969959+00:00
-- url     : https://prove2.me/theorems/e7eceeb9-ee0e-4830-bad3-2009f8d3be35
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 3
-- statement:
--   For prepared pair 24, right list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 320 through 343, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_002Part03.lean, lines 11-16, SHA-256 6acead48b81e2ab07e5b9ba9469b86fe1b3aeed3d055b1e6b4b5872f69f41e0b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.rightCached.drop 320)
      (PairLightPrepared24.rightRows.drop 320) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
