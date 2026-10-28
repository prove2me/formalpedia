-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:05.452151+00:00
-- url     : https://prove2.me/theorems/e34c97fa-a0cd-4d27-bf9c-9505417dcf4e
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 4
-- statement:
--   For prepared pair 21, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 232 through 243, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_002Part04.lean, lines 10-14, SHA-256 396a9646146897232cfec32281c3f4d13b540510067ff689c5f0ab6ade48e9c7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_002_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 232) (PairLightPrepared21.leftRows.drop 232) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
