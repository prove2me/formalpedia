-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:44.881673+00:00
-- url     : https://prove2.me/theorems/05f3389e-dc3a-4ca6-a67c-bdc1e846c29d
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 4
-- statement:
--   For prepared pair 23, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 48 through 59, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_000Part04.lean, lines 10-14, SHA-256 d1fbe15ae0e2b9be9b8391c32062a9b8796457f45dce9d0967318eaad122faf3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 48) (PairLightPrepared23.leftRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
