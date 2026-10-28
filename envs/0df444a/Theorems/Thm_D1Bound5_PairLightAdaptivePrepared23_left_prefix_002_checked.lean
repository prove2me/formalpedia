-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:19.051983+00:00
-- url     : https://prove2.me/theorems/90d0cfd9-983a-4962-b485-7feb96313de2
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list
-- statement:
--   For prepared pair 23, left list, the selected-floor certificate succeeds for at most `270` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft23_002.lean, lines 31-168, SHA-256 5c65973953713c94ac91c2f6f937ea9af72fb90e5249ece1df2cdf21aa3e1c7e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 270
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
