-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:37:44.84899+00:00
-- url     : https://prove2.me/theorems/61f06e97-46f6-44b6-b70c-89acfff8102e
-- title:
--   Selected-floor prefix certificate for prepared pair 3, right list
-- statement:
--   For prepared pair 3, right list, the selected-floor certificate succeeds for at most `195` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight3Prefix001.lean, lines 16-69, SHA-256 6674d07b070724295e33cefe45aea50e6a1f0572bab7d2b73f053f06eb8dea40. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 195
      (PairLightPrepared3.rightCached.drop 111) (PairLightPrepared3.rightRows.drop 111) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared3
end
