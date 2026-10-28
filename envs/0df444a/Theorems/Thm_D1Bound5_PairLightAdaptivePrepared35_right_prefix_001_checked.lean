-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:25.332306+00:00
-- url     : https://prove2.me/theorems/02334da2-8b95-4308-b18c-a1a104194357
-- title:
--   Selected-floor prefix certificate for prepared pair 35, right list
-- statement:
--   For prepared pair 35, right list, the selected-floor certificate succeeds for at most `236` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Heads 132 through 367; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight35_001.lean, lines 11-29, SHA-256 f7db5feb5d79f88dec3de941701c34110f4c068630c8928c08a24e474b538d67. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 236
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
