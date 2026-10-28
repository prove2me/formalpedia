-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:47.236748+00:00
-- url     : https://prove2.me/theorems/1951fb54-f945-493c-805f-f1798e5683d5
-- title:
--   Selected-floor prefix certificate for prepared pair 12, right list
-- statement:
--   For prepared pair 12, right list, the selected-floor certificate succeeds for at most `138` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Heads 0 through 137; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight12_000.lean, lines 13-43, SHA-256 a92c6db7bdb6502ecd261da04e876820fc45eb931d43f03cdac142ff6b25d989. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 138
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
