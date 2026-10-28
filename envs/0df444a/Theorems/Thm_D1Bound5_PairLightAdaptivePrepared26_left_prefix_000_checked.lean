-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:51.953274+00:00
-- url     : https://prove2.me/theorems/0bd06044-207a-4100-9889-9e15174cc803
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list
-- statement:
--   For prepared pair 26, left list, the selected-floor certificate succeeds for at most `54` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 0 through 53; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_000.lean, lines 24-132, SHA-256 969136bca8f590bcadc0bb6cc64b358a5dd10b127120fd7827d21aca0a2406b7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 54
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
