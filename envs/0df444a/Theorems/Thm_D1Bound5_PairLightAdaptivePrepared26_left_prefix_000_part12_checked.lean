-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:53:21.141688+00:00
-- url     : https://prove2.me/theorems/2ab1b794-8276-47e6-8cf8-bfba0ca63f94
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 12
-- statement:
--   For prepared pair 26, left list, part 12, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 36 through 38 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_000Part12.lean, lines 7-11, SHA-256 e08cc1df5034c29df49451d54fd3f8b3d862d8ef9a3e54e0fa86ff5b5ab42a04. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part12_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached000.drop 36) (leftRows000.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
