-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:21.034446+00:00
-- url     : https://prove2.me/theorems/5e84d99c-104f-4464-ad99-ad2faa8d8092
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 14
-- statement:
--   For prepared pair 28, right list, part 14, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 503 through 514, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_003Part14.lean, lines 10-14, SHA-256 57894004da95ee70810af4158ad48e0de0feed75b1386fd932c3b52da5cb16fc. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part14_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 503) (PairLightPrepared28.rightRows.drop 503) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
