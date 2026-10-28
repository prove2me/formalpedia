-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:15.500838+00:00
-- url     : https://prove2.me/theorems/8c655a26-ec5f-4f0f-b048-a45e7218887e
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 8
-- statement:
--   For prepared pair 36, right list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 383 through 394, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part08.lean, lines 10-14, SHA-256 a463b6860ae4806d7ebd192378cd4a3cdedefaacf8d9eb6164bb7be228e54634. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part08_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 383) (PairLightPrepared36.rightRows.drop 383) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
