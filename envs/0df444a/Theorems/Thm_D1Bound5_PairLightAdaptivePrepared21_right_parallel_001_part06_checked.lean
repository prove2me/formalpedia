-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:00.55695+00:00
-- url     : https://prove2.me/theorems/86987381-8b39-4222-8dbb-344a86d9d8bc
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 6
-- statement:
--   For prepared pair 21, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 154 through 165, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_001Part06.lean, lines 10-14, SHA-256 ca5254565453b46575205fe6c5097ebe5d63140c7564eb226b9178ae163feef8. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_001_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 154) (PairLightPrepared21.rightRows.drop 154) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
