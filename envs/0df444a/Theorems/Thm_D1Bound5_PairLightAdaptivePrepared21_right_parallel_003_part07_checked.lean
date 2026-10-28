-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_003_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:54.195899+00:00
-- url     : https://prove2.me/theorems/7cb805a7-0ea6-4440-9b76-6311c5197b1c
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 7
-- statement:
--   For prepared pair 21, right list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 419 through 430, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_003Part07.lean, lines 10-14, SHA-256 7fc00b6989d680ea6ec798985d8501c582eeb526be2e7fecba92ed46aaedb5d5. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 419) (PairLightPrepared21.rightRows.drop 419) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
