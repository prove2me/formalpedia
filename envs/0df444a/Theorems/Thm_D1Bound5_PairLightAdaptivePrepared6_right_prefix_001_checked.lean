-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:40.456981+00:00
-- url     : https://prove2.me/theorems/ac3f70fe-e041-4b46-9005-4c5b2e6cc846
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list
-- statement:
--   For prepared pair 6, right list, the selected-floor certificate succeeds for at most `71` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_001.lean, lines 15-50, SHA-256 092926b53585ee8f8b02c41ee662dbe4ec217e241d6da7d750fbc561d8fd220a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 71
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
