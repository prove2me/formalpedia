-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:43.469988+00:00
-- url     : https://prove2.me/theorems/0ff39fbe-00d6-4b75-ab69-cd107af98e7a
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 1
-- statement:
--   For prepared pair 36, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 12 through 23, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_000Part01.lean, lines 10-14, SHA-256 08c47734e89f13bf2adca763c7e8419e1d5adc398759b2b881c5c3e25704ab2c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 12) (PairLightPrepared36.rightRows.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
