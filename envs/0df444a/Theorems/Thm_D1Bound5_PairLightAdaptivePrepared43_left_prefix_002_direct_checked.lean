-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:43.141873+00:00
-- url     : https://prove2.me/theorems/18b19ad1-89d0-431a-b802-e0e56bb73ab5
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list
-- statement:
--   For prepared pair 43, left list, the selected-floor certificate succeeds for at most `270` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft43Prefix002.lean, lines 19-90, SHA-256 3378a9f3830c31b4b7fd83ad81dc31848f5adbe7460ac51e4e66973a6fa715bb. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 270
      (PairLightPrepared43.leftCached.drop 212) (PairLightPrepared43.leftRows.drop 212) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared43
end
