-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_003_part15_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:36.005865+00:00
-- url     : https://prove2.me/theorems/8375af2a-1dfc-41e6-bb72-a99c522e5953
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 15
-- statement:
--   For prepared pair 28, left list, part 15, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 515 through 523, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_003Part15.lean, lines 10-14, SHA-256 e19533d61ec9f9f4610abbf5bf8e971c3e9a6ca47ae330ae196c834456286d2e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part15_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 9
      (PairLightPrepared28.leftCached.drop 515) (PairLightPrepared28.leftRows.drop 515) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
