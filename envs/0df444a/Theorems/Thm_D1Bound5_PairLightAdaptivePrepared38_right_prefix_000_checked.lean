-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:18.310447+00:00
-- url     : https://prove2.me/theorems/b2550a67-2616-46ad-9612-c632ee700610
-- title:
--   Selected-floor prefix certificate for prepared pair 38, right list
-- statement:
--   For prepared pair 38, right list, the selected-floor certificate succeeds for at most `281` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared38.sieve`. Heads 0 through 280; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight38_000.lean, lines 12-36, SHA-256 f6fb02579c225e576ba29759eed44f0b7a2384c2c498a832d4e51a0986f56fd4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 281
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared38
end
