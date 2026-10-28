-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:48.191561+00:00
-- url     : https://prove2.me/theorems/2caf3b0b-f618-4782-a68b-a034849ef5d0
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 7
-- statement:
--   For prepared pair 28, right list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 268 through 279, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_002Part07.lean, lines 10-14, SHA-256 28f09aa64d1c823812d0f805d09aa269ad66a84e1a88317b69d0507a3aba6308. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 268) (PairLightPrepared28.rightRows.drop 268) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
