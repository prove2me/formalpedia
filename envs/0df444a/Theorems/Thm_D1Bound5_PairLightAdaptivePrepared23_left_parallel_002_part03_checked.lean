-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:52.094873+00:00
-- url     : https://prove2.me/theorems/e306f7f4-9fa2-42e8-85c1-893d58b641ab
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 3
-- statement:
--   For prepared pair 23, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 248 through 259, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_002Part03.lean, lines 10-14, SHA-256 9600902aa027a612f09ea788be161bdaeee34d14d4ff714bb08913084e3b83fc. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 248) (PairLightPrepared23.leftRows.drop 248) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
