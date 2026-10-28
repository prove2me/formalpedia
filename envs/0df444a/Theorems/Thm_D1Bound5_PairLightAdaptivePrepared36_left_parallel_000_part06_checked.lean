-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:17.704925+00:00
-- url     : https://prove2.me/theorems/42cc6db8-74c9-482e-8a12-ccba215e9772
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 6
-- statement:
--   For prepared pair 36, left list, part 6, the selected-floor certificate succeeds for at most `4` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 72 through 75, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_000Part06.lean, lines 10-14, SHA-256 0da4009948c9b132efcb50b8fe5a14fd421d581ae665ab6c02c6da60d7f2143c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 4
      (PairLightPrepared36.leftCached.drop 72) (PairLightPrepared36.leftRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
