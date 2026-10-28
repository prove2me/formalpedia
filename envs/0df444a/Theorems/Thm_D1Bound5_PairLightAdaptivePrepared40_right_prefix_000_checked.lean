-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:17.118045+00:00
-- url     : https://prove2.me/theorems/54d374b5-27a1-4692-8562-a10f60511571
-- title:
--   Selected-floor prefix certificate for prepared pair 40, right list
-- statement:
--   For prepared pair 40, right list, the selected-floor certificate succeeds for at most `138` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Heads 0 through 137; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight40_000.lean, lines 13-43, SHA-256 1de25fa59e0a8ba80fb3e5c64ac69a3242c198d0cc465258d212b030014abd27. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 138
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
