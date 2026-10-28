-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:36.119637+00:00
-- url     : https://prove2.me/theorems/1b5aabd8-1480-45b3-baa1-6ca5e8af4dbc
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list
-- statement:
--   For prepared pair 28, right list, the selected-floor certificate succeeds for at most `189` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight28_003.lean, lines 24-119, SHA-256 d812499c1895bf741d5e3fe2f2990767e4a5d568a82cd203eeb1129121e466d5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 189
      rightCached003 rightRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
