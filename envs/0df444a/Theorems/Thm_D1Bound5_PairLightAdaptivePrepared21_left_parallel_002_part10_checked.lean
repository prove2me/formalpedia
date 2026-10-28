-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_002_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_002_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:12.269893+00:00
-- url     : https://prove2.me/theorems/d75e0cde-a4a9-46b8-9c0f-bb3cbb6a4bcf
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 10
-- statement:
--   For prepared pair 21, left list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 304 through 315, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_002Part10.lean, lines 10-14, SHA-256 d40a77d4afe66dc326cc4e000d77a9e5a1f5d55c9414bc577f5b6f8a7117a624. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_002_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 304) (PairLightPrepared21.leftRows.drop 304) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
