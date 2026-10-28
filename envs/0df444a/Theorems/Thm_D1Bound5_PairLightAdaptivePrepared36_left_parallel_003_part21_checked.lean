-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part21_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part21_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:48.902606+00:00
-- url     : https://prove2.me/theorems/8b6d8ad2-c8ad-4215-ab11-78d7d368908a
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 21
-- statement:
--   For prepared pair 36, left list, part 21, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 538 through 549, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part21.lean, lines 10-14, SHA-256 a00241001bc0b1f7c18a128c4a59c4433c936233d27a2c2481b6b30527180155. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part21_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 538) (PairLightPrepared36.leftRows.drop 538) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
