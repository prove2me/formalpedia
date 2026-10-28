-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:11.037369+00:00
-- url     : https://prove2.me/theorems/52bb2226-a5e6-4f9e-8a8a-a82afa4823ff
-- title:
--   Selected-floor prefix certificate for prepared pair 35, right list
-- statement:
--   For prepared pair 35, right list, the selected-floor certificate succeeds for at most `132` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Heads 0 through 131; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight35_000.lean, lines 13-43, SHA-256 eee760c04602493fd196471a90c6a2be6b437d40013650cfde19dbdd67b142cd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 132
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
