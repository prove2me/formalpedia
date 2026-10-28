-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:40.607417+00:00
-- url     : https://prove2.me/theorems/739f23b6-598f-41ca-a015-404a1671c78e
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list
-- statement:
--   For prepared pair 4, right list, the selected-floor certificate succeeds for at most `102` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_002.lean, lines 15-50, SHA-256 108238b7164c06703c69fb30f99c3d21cad7579c9b3cda1a0cb72c576708991b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 102
      rightCached002 rightRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
