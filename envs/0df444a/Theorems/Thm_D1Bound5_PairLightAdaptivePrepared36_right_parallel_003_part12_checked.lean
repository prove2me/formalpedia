-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:55.188897+00:00
-- url     : https://prove2.me/theorems/103164fc-6053-439e-9408-30d3619e51e6
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 12
-- statement:
--   For prepared pair 36, right list, part 12, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 431 through 442, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part12.lean, lines 10-14, SHA-256 321bc368a220ff011d2f9b97077e74f48630a0081cd03bcf3d4054cfd5c975ae. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part12_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 431) (PairLightPrepared36.rightRows.drop 431) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
