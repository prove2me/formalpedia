-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:07.990019+00:00
-- url     : https://prove2.me/theorems/e6e909a7-5237-4815-8449-b892f5085a41
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list
-- statement:
--   For prepared pair 14, right list, the selected-floor certificate succeeds for at most `215` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight14_002.lean, lines 26-133, SHA-256 104839406a3d35c5352aded0da14817b7bf7c983d5ebe695cc8acc9b28e0d454. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 215
      rightCached002 rightRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
