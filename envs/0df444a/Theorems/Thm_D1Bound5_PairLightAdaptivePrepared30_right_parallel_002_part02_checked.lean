-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:09.532198+00:00
-- url     : https://prove2.me/theorems/1f69e303-fa0d-4763-9469-40a2ee81fe9d
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 2
-- statement:
--   For prepared pair 30, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 238 through 249, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_002Part02.lean, lines 10-14, SHA-256 8bfb4ff7f32461e912abf258c82dd89711cbb4e9fb8e3e77c159048d552e285b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 238) (PairLightPrepared30.rightRows.drop 238) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
