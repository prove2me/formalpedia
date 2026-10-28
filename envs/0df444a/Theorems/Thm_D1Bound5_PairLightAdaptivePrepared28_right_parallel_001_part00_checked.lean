-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:53:15.112032+00:00
-- url     : https://prove2.me/theorems/f911e1b5-6029-40e7-8f5b-49f317bf1ba5
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 0
-- statement:
--   For prepared pair 28, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 82 through 93, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_001Part00.lean, lines 10-14, SHA-256 5bc8f134bab8255596fbf8d1f952a72b8acb509d00b943a5045f7b6c5a75a6c9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 82) (PairLightPrepared28.rightRows.drop 82) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
