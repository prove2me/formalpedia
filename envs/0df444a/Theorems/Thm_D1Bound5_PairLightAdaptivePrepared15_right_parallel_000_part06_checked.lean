-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:59.72861+00:00
-- url     : https://prove2.me/theorems/63c4a55d-1c9c-4746-9525-97bfc3b61bb7
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 6
-- statement:
--   For prepared pair 15, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 72 through 83, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_000Part06.lean, lines 10-14, SHA-256 82b5d1cff6b568714046b99adc2534d4492080cf6a7cad8a9c90f9a5e36927e3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part06_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 72) (PairLightPrepared15.rightRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
