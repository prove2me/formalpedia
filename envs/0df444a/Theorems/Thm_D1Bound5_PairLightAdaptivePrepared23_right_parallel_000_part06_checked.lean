-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:39.700325+00:00
-- url     : https://prove2.me/theorems/57ff9234-a59d-4753-aa37-a5b3fd9c1642
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 6
-- statement:
--   For prepared pair 23, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 72 through 83, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_000Part06.lean, lines 10-14, SHA-256 fc79f89da899572f1ea7c1b205b49548b3cb0f50e725014e82f9a0f54ab550fb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 72) (PairLightPrepared23.rightRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
