-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:41.312561+00:00
-- url     : https://prove2.me/theorems/abb25fd8-7931-4c99-b162-db0b8b72da64
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 8
-- statement:
--   For prepared pair 23, left list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 187 through 198, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_001Part08.lean, lines 10-14, SHA-256 2836d619eb9bbf565d01e759445601775e2fd3afb70bbe29ab380c102fa44848. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 187) (PairLightPrepared23.leftRows.drop 187) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
