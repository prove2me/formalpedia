-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:57.491684+00:00
-- url     : https://prove2.me/theorems/b2fb6e9d-5427-46b6-b915-0d6323b29d3d
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 2
-- statement:
--   For prepared pair 21, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 208 through 219, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_002Part02.lean, lines 10-14, SHA-256 db56782f7842f66fd8aa53bb074a893136ffea315e777ad98329f6d2bc990198. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_002_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 208) (PairLightPrepared21.leftRows.drop 208) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
