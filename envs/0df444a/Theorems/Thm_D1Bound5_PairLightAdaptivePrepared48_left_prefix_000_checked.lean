-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:41.019058+00:00
-- url     : https://prove2.me/theorems/916cd49a-0e9a-4452-8e29-1a53ee733e9c
-- title:
--   Selected-floor prefix certificate for prepared pair 48, left list
-- statement:
--   For prepared pair 48, left list, the selected-floor certificate succeeds for at most `137` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Heads 0 through 136; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft48_000.lean, lines 13-43, SHA-256 a1e2884f0ef52fd0a986a3675bc15f50c66e2cfce48aa2a5bacaffdbe68c396a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 137
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
