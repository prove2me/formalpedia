-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part16_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part16_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:06.415615+00:00
-- url     : https://prove2.me/theorems/ec96141b-a302-4816-8749-09005ba482be
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 16
-- statement:
--   For prepared pair 36, right list, part 16, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 479 through 490, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part16.lean, lines 10-14, SHA-256 0b96649ed058942e18889062a78a3dd3074e204d73a844710243e22193205898. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part16_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 479) (PairLightPrepared36.rightRows.drop 479) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
