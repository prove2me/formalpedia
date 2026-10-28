-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:51.241471+00:00
-- url     : https://prove2.me/theorems/381c9b0d-1baf-4391-94c9-dc4ec6410728
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list
-- statement:
--   For prepared pair 36, left list, the selected-floor certificate succeeds for at most `119` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft36_002.lean, lines 18-77, SHA-256 e9531b1364f3d06955d17dce04b3f179a0a5f31a4a36101d8ec19277b6377b50. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 119
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
