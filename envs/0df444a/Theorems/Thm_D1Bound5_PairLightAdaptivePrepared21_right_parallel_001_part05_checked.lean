-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T05:57:48.574988+00:00
-- url     : https://prove2.me/theorems/503f0462-13b8-47bf-91b9-f3812ac8d047
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 5
-- statement:
--   For prepared pair 21, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 142 through 153, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_001Part05.lean, lines 10-14, SHA-256 d14e7057962486782aa5b161c704d3e80229c5699a9086f6e9d36b5e1f3f50ea. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 142) (PairLightPrepared21.rightRows.drop 142) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
