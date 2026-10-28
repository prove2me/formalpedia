-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:03.689079+00:00
-- url     : https://prove2.me/theorems/37c83f36-7106-4256-a6d3-ccfd5eb13a7a
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 4
-- statement:
--   For prepared pair 14, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 48 through 59, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_000Part04.lean, lines 10-14, SHA-256 5476b041e7a4957f1022f76fbe8c6f98746f5755579ca0bc62ae50ff93ee5e38. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 48) (PairLightPrepared14.rightRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
