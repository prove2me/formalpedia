-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_002_part11_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:55.838482+00:00
-- url     : https://prove2.me/theorems/e496462f-04b9-4ecb-9e8d-07b270112412
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 11
-- statement:
--   For prepared pair 21, right list, part 11, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 316 through 327, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_002Part11.lean, lines 10-14, SHA-256 b8fc514d40c92b77e89ae2f0113480fdcc331bd7c107be82302e1647b10b3811. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part11_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 316) (PairLightPrepared21.rightRows.drop 316) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
