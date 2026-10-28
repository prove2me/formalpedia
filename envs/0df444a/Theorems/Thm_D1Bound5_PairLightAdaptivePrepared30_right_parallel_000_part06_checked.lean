-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:57:59.301133+00:00
-- url     : https://prove2.me/theorems/d5f6f88b-7bac-41a8-a140-e4e3d4051ef1
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 6
-- statement:
--   For prepared pair 30, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 72 through 83, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_000Part06.lean, lines 10-14, SHA-256 b46a8bfa5b4ed444e531f737eee104e8688ef7227feb6eac93be4ffefc45d1a4. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 72) (PairLightPrepared30.rightRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
