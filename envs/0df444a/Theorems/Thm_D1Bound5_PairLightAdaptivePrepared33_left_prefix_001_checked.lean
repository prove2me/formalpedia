-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared33.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:32.999162+00:00
-- url     : https://prove2.me/theorems/4fe6f047-42e3-4d95-9645-72f6cf5fd92f
-- title:
--   Selected-floor prefix certificate for prepared pair 33, left list
-- statement:
--   For prepared pair 33, left list, the selected-floor certificate succeeds for at most `223` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared33.sieve`. Heads 137 through 359; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft33_001.lean, lines 11-29, SHA-256 98e312669f291a404da19822f9164bf0032ee5b3795bde9a9f417c3f361b9289. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared33.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 223
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared33
end
