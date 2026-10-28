-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:42.425012+00:00
-- url     : https://prove2.me/theorems/31516f59-1370-49df-b892-56efcb4cfb9d
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 0
-- statement:
--   For prepared pair 30, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 0 through 11, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_000Part00.lean, lines 10-14, SHA-256 d6388553f8228688fcb0c5ae840e1ee1f8791718862abda21d9ab32b2a81396b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 0) (PairLightPrepared30.leftRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
