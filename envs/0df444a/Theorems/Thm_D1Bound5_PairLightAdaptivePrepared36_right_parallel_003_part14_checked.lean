-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:25.214079+00:00
-- url     : https://prove2.me/theorems/4a089b7d-da81-4cca-a388-ea92dab08e9f
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 14
-- statement:
--   For prepared pair 36, right list, part 14, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 455 through 466, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part14.lean, lines 10-14, SHA-256 fd3f9f6203595f87f585fde3c1282af5a34d785582f167136667a405cd998ea2. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part14_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 455) (PairLightPrepared36.rightRows.drop 455) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
