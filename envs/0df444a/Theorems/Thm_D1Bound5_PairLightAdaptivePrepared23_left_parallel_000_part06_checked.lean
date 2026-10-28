-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:48.039522+00:00
-- url     : https://prove2.me/theorems/ba49bd91-5517-4b20-b4f4-ba588fcf9ee8
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 6
-- statement:
--   For prepared pair 23, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 72 through 83, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_000Part06.lean, lines 10-14, SHA-256 bc81f136b80427e8225ea671b0fe3b0ff12fdc766e25f0b688dd350b7e94581c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 72) (PairLightPrepared23.leftRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
