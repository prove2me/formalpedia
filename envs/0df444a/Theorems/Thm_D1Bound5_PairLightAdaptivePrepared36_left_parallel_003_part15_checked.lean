-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part15_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:12.195793+00:00
-- url     : https://prove2.me/theorems/3bc1967d-25aa-4b23-825f-66970f864b56
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 15
-- statement:
--   For prepared pair 36, left list, part 15, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 466 through 477, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part15.lean, lines 10-14, SHA-256 03afe70a2350548c59c9862138ac5e68fd627b8220adcb4642d02eff9bb81419. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part15_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 466) (PairLightPrepared36.leftRows.drop 466) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
