-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_003_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:04.750069+00:00
-- url     : https://prove2.me/theorems/9fc2be1c-b2e8-49a3-8ca6-79f8f190a67c
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 4
-- statement:
--   For prepared pair 28, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 383 through 394, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_003Part04.lean, lines 10-14, SHA-256 5b4e6c94c84026b982322417e79dc2160821ae2b29b88ea42250db879cbe50ce. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 383) (PairLightPrepared28.leftRows.drop 383) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
