-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:16.609983+00:00
-- url     : https://prove2.me/theorems/39ab89c0-d6a5-48c0-acaf-26d12311e961
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 8
-- statement:
--   For prepared pair 26, left list, part 8, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 24 through 26 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_000Part08.lean, lines 7-11, SHA-256 bf7e722d1ec217c8285922e3e8fe483b2b52b6e79b4b67fd44bd9305ee3c4ce6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached000.drop 24) (leftRows000.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
