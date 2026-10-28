-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:21.825981+00:00
-- url     : https://prove2.me/theorems/6afb7163-22ef-4822-85b5-4995dd0151ab
-- title:
--   Selected-floor prefix certificate for prepared pair 17, right list
-- statement:
--   For prepared pair 17, right list, the selected-floor certificate succeeds for at most `138` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Heads 0 through 137; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight17_000.lean, lines 13-43, SHA-256 f36af453b3677a07143322604887fffd2ad0b50809068a37f52ee2eaddb88784. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 138
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
