-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:36.449298+00:00
-- url     : https://prove2.me/theorems/6de232f5-b231-4f5c-8f04-1176fb2c7a16
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 6
-- statement:
--   For prepared pair 36, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 239 through 250, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_002Part06.lean, lines 10-14, SHA-256 84b4b4148c041984ea4ac62b8151d9ab2077f79ab3c9b8cb6ba5833580b5a20a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_002_part06_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 239) (PairLightPrepared36.leftRows.drop 239) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
