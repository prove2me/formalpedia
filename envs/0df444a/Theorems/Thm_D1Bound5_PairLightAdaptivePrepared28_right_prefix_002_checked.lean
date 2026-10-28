-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:13.250752+00:00
-- url     : https://prove2.me/theorems/15ca1d50-830d-4f5a-808b-c7323935cd82
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list
-- statement:
--   For prepared pair 28, right list, the selected-floor certificate succeeds for at most `151` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight28_002.lean, lines 21-98, SHA-256 7d2f19f093e5f644f2a013d10bbbc2eebe7c6804f78a1c8e112a676665cf995c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 151
      rightCached002 rightRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
