-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:22.346846+00:00
-- url     : https://prove2.me/theorems/a443c92f-7d2f-4513-bd40-ec534d75d50f
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 2
-- statement:
--   For prepared pair 23, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 24 through 35, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_000Part02.lean, lines 10-14, SHA-256 450dc4f319cf2e73853ec3698239229cac7d76fadd39c69e1f1a9f92e27283eb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 24) (PairLightPrepared23.rightRows.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
