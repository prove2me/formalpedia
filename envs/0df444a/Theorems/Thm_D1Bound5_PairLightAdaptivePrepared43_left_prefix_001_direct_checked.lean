-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:53.174925+00:00
-- url     : https://prove2.me/theorems/e3dd1b09-269c-4a36-ab10-ab3dc0bed08f
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list
-- statement:
--   For prepared pair 43, left list, the selected-floor certificate succeeds for at most `121` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft43Prefix001.lean, lines 18-83, SHA-256 0bfd1347c446f1b37eb53a442828515322bbb0296c06a2b15c1744c53389df48. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 121
      (PairLightPrepared43.leftCached.drop 91) (PairLightPrepared43.leftRows.drop 91) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared43
end
