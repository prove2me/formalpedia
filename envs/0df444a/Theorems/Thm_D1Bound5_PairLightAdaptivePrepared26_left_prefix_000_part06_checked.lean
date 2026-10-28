-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:38.441864+00:00
-- url     : https://prove2.me/theorems/df105292-9e3d-4b9c-b01f-9d6c4bb61f70
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 6
-- statement:
--   For prepared pair 26, left list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 18 through 20 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_000Part06.lean, lines 7-11, SHA-256 fd7448ca74ec5402531c799c94c54c389777247cd75aa4905983e2869e99ac14. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached000.drop 18) (leftRows000.drop 18) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
