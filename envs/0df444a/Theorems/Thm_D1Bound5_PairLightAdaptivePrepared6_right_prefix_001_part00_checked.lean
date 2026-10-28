-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:15.105985+00:00
-- url     : https://prove2.me/theorems/108f44c8-8930-4c5d-b341-9c37f1d381fe
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 0
-- statement:
--   For prepared pair 6, right list, part 0, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 64 through 74, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_001Part00.lean, lines 11-16, SHA-256 f1a4b40b3e12a81a41d1e702c7fc055b74d99247e1e5d3bbdf407c87ebcdc3eb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 11
      (PairLightPrepared6.rightCached.drop 64)
      (PairLightPrepared6.rightRows.drop 64) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
