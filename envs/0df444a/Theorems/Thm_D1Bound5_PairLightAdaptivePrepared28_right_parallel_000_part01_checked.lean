-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:57.473606+00:00
-- url     : https://prove2.me/theorems/f9a20859-5cd1-4936-b442-dd63fee09935
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 1
-- statement:
--   For prepared pair 28, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 12 through 23, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_000Part01.lean, lines 10-14, SHA-256 03a48b71a9617262e2be98a6ef7c2faadbbbdc4b097257b5691bd08245736c93. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 12) (PairLightPrepared28.rightRows.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
