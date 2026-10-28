-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_003_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:56.646767+00:00
-- url     : https://prove2.me/theorems/14e014fd-ff5f-40d8-9c5e-1e22c16dce95
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 13
-- statement:
--   For prepared pair 21, right list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 491 through 502, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_003Part13.lean, lines 10-14, SHA-256 8fd3ad561753040ea32e074c91653233673d8792c2a0d47a2f22a7c4c3b538e5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part13_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 491) (PairLightPrepared21.rightRows.drop 491) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
