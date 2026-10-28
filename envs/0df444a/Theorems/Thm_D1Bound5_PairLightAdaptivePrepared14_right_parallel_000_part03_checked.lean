-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:41.029721+00:00
-- url     : https://prove2.me/theorems/343e39a1-67cf-4fc4-802a-eb264519a43c
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 3
-- statement:
--   For prepared pair 14, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 36 through 47, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_000Part03.lean, lines 10-14, SHA-256 5f0e00046ed5bdd1ee3ec6d8b792bdb4acb5d11c1ff32f15ef657422377af676. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 36) (PairLightPrepared14.rightRows.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
