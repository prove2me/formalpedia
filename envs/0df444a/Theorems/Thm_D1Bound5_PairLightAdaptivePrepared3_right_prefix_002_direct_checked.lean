-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.right_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:50:01.122548+00:00
-- url     : https://prove2.me/theorems/9bdd5caf-c8ab-4c5a-865e-057f5b60244e
-- title:
--   Selected-floor prefix certificate for prepared pair 3, right list
-- statement:
--   For prepared pair 3, right list, the selected-floor certificate succeeds for at most `108` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight3Prefix002.lean, lines 12-41, SHA-256 beef6b269245ea955e244e0f581ffcfae7348a15b43342770b32322a7e31c1bc. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared3.right_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 108
      (PairLightPrepared3.rightCached.drop 306) (PairLightPrepared3.rightRows.drop 306) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared3
end
