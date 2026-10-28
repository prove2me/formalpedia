-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:38.480542+00:00
-- url     : https://prove2.me/theorems/0ad6e0b7-4a74-4704-a470-94c5038d77c5
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 2
-- statement:
--   For prepared pair 28, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 106 through 117, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_001Part02.lean, lines 10-14, SHA-256 c203decf72ad518bb79887b39e72c72e43421b9dba999be4014014e05f463aa9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 106) (PairLightPrepared28.rightRows.drop 106) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
