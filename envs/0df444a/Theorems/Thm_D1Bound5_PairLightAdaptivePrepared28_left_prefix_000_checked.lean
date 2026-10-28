-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:11.68889+00:00
-- url     : https://prove2.me/theorems/c21ca969-c1ee-4589-8b69-23d490d2e6e5
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list
-- statement:
--   For prepared pair 28, left list, the selected-floor certificate succeeds for at most `82` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft28_000.lean, lines 15-56, SHA-256 90f484d8fdb82f34c95bb5d68758ed855a0e9dfdb90a7e644cc116b5e919bf32. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 82
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
