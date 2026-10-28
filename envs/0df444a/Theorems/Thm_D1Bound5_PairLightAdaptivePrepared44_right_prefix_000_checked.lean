-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared44_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared44.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:53.107969+00:00
-- url     : https://prove2.me/theorems/889967b0-89d7-4722-b58e-2997fce04e2a
-- title:
--   Selected-floor prefix certificate for prepared pair 44, right list
-- statement:
--   For prepared pair 44, right list, the selected-floor certificate succeeds for at most `220` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 4, and the sieve is `PairLightPrepared44.sieve`. Heads 0 through 219; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight44_000.lean, lines 7-11, SHA-256 808ee9eaac8d615a994dbada184ce8298264f295c38aeeb931f2366e0c8e8771. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData44_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared44.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 4 PairLightPrepared44.sieve 220
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared44
end
