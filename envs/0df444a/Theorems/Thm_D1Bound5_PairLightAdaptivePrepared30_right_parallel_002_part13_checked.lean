-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_002_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:27.979878+00:00
-- url     : https://prove2.me/theorems/8c204fff-5aae-4204-98ea-88ce854ed80c
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 13
-- statement:
--   For prepared pair 30, right list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 370 through 381, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_002Part13.lean, lines 10-14, SHA-256 e619a3699ef141fc04c4ce52741e1962e21b93587f39808c62f879b26a26796c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part13_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 370) (PairLightPrepared30.rightRows.drop 370) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
