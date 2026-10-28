-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:39.379513+00:00
-- url     : https://prove2.me/theorems/2a38107e-05f7-4e6d-8ee1-f0b8a4f2f5f4
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 4
-- statement:
--   For prepared pair 36, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 48 through 59, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_000Part04.lean, lines 10-14, SHA-256 e934e98e4a71e2fd95ee437827cdd6614de5da8a74b5c40d0416a52d2d81ca6e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 48) (PairLightPrepared36.leftRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
