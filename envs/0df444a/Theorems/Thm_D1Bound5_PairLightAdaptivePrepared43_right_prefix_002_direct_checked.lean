-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:50.052504+00:00
-- url     : https://prove2.me/theorems/56142df9-ca93-47f1-9e48-d57f0e3ce229
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list
-- statement:
--   For prepared pair 43, right list, the selected-floor certificate succeeds for at most `266` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight43Prefix002.lean, lines 19-90, SHA-256 f5ea97dd563d9786e4a68ffc3983f87b15e5c84dc13b7ac2dd76e75da4c95484. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 266
      (PairLightPrepared43.rightCached.drop 214) (PairLightPrepared43.rightRows.drop 214) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared43
end
