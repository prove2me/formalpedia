-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:41:35.148576+00:00
-- url     : https://prove2.me/theorems/db5d3270-f136-4090-9bc3-a2ea23740da6
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list
-- statement:
--   For prepared pair 26, left list, the selected-floor certificate succeeds for at most `65` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Exact original head block; every head retains its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002.lean, lines 28-160, SHA-256 1f3f55c6bec89bc9d85c89d9404a5a08128db99fa693e6984344ec50377bc137. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 65
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
