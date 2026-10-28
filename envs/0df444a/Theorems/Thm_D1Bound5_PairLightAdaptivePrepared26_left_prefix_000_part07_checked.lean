-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:24.32622+00:00
-- url     : https://prove2.me/theorems/957d28d4-7d81-40fe-a363-e7b132308506
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 7
-- statement:
--   For prepared pair 26, left list, part 7, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 21 through 23 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_000Part07.lean, lines 7-11, SHA-256 3afcf7d7186d21668ae6223955ce17d18b1918dd5bb1feb3318edf5f8e42a1b4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached000.drop 21) (leftRows000.drop 21) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
