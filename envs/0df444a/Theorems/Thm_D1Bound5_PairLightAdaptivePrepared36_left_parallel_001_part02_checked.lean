-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:08.810163+00:00
-- url     : https://prove2.me/theorems/45fbd562-9e11-40dd-8a02-6e4a932864af
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 2
-- statement:
--   For prepared pair 36, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 100 through 111, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_001Part02.lean, lines 10-14, SHA-256 7a09af74ab2a6ff8bdc84328a1c24474c69370ca75a404a35749ed248a6229ac. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 100) (PairLightPrepared36.leftRows.drop 100) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
