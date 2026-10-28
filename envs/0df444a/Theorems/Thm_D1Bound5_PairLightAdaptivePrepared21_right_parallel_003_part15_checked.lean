-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_003_part15_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:22.497579+00:00
-- url     : https://prove2.me/theorems/9025068b-5a6c-4748-a5a5-e9a12d4d2b5c
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 15
-- statement:
--   For prepared pair 21, right list, part 15, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 515 through 523, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_003Part15.lean, lines 10-14, SHA-256 33a76cbdaa68bc9692898b2b9af93cb2c9b6eee032ce2d03098911e7c12f9b04. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part15_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 9
      (PairLightPrepared21.rightCached.drop 515) (PairLightPrepared21.rightRows.drop 515) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
