-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_003_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:57.2456+00:00
-- url     : https://prove2.me/theorems/7dffb610-fa0c-4c81-b355-98b32444f1ce
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 0
-- statement:
--   For prepared pair 21, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 335 through 346, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_003Part00.lean, lines 10-14, SHA-256 4ec050098f15d5c056dc20fd894b71acf2ffd7003f3f81c198a882feec543c2e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 335) (PairLightPrepared21.rightRows.drop 335) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
