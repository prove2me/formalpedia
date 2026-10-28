-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared45.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:13.24413+00:00
-- url     : https://prove2.me/theorems/ee77e053-f524-40d6-b7f2-4e13f403319b
-- title:
--   Selected-floor prefix certificate for prepared pair 45, left list
-- statement:
--   For prepared pair 45, left list, the selected-floor certificate succeeds for at most `43` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 5, and the sieve is `PairLightPrepared45.sieve`. Heads 0 through 42; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft45_000.lean, lines 7-11, SHA-256 42a7053b690d02deb535d32e2cf5df98fa08f817ab95b06ae09eee6d76630b44. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData45_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared45.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 5 PairLightPrepared45.sieve 43
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared45
end
