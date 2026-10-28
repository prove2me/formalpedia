-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_001_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:34.090832+00:00
-- url     : https://prove2.me/theorems/8908b6fe-3dfb-4398-8cc8-ed2379e103d5
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 7
-- statement:
--   For prepared pair 23, right list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 176 through 187, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_001Part07.lean, lines 10-14, SHA-256 58719a8afd92a122aaf29efa51529214eeddd93fd6653c014c37c6d24231d3d3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 176) (PairLightPrepared23.rightRows.drop 176) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
