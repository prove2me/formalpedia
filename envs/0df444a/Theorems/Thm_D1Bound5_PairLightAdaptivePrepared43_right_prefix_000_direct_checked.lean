-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:14.141989+00:00
-- url     : https://prove2.me/theorems/a174b109-8aad-4e1d-89a3-083fd770e163
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list
-- statement:
--   For prepared pair 43, right list, the selected-floor certificate succeeds for at most `92` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight43Prefix000.lean, lines 15-62, SHA-256 52eb733894e02f2ea264631a58bc6f6b3eeb5de518da9f5a2ebb4a8e87059aa5. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 92
      (PairLightPrepared43.rightCached.drop 0) (PairLightPrepared43.rightRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared43
end
