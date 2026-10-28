-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:41:18.722987+00:00
-- url     : https://prove2.me/theorems/89c76680-4bd8-4f91-806b-ffdb75c44128
-- title:
--   Selected-floor prefix certificate for prepared pair 29, left list
-- statement:
--   For prepared pair 29, left list, the selected-floor certificate succeeds for at most `254` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft29_001.lean, lines 12-35, SHA-256 7edef042d12b59268973db34a17fa32118aa2f7df125440232b47a32ee16d28b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 254
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
