-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:47.301478+00:00
-- url     : https://prove2.me/theorems/d3177f65-540d-4f57-8477-257c9772b5f8
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 7
-- statement:
--   For prepared pair 23, right list, part 7, the selected-floor certificate succeeds for at most `8` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 84 through 91, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_000Part07.lean, lines 10-14, SHA-256 5b8f114dc95a30e3124c819561f3ad7fa3b56b3930fc10f33265d41dbba2aa49. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_000_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 8
      (PairLightPrepared23.rightCached.drop 84) (PairLightPrepared23.rightRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
