-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_003_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:53.186991+00:00
-- url     : https://prove2.me/theorems/9dbd1110-e0b0-4a9f-9089-fe2564c22bb6
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 7
-- statement:
--   For prepared pair 21, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 419 through 430, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_003Part07.lean, lines 10-14, SHA-256 03b00b54d490b71980021f650fea3d95e05ad0c27a23d682dc4ddba7cc86c594. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 419) (PairLightPrepared21.leftRows.drop 419) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
