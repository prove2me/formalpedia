-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:49.013792+00:00
-- url     : https://prove2.me/theorems/2cfcc452-eb4b-466e-9d94-a60bb809e92e
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 2
-- statement:
--   For prepared pair 30, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 24 through 35, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_000Part02.lean, lines 10-14, SHA-256 c2362e205ac5c618fa52c169b90ae11390e2ba0cb0bfc3e61989fd2d78b7f55c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 24) (PairLightPrepared30.rightRows.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
