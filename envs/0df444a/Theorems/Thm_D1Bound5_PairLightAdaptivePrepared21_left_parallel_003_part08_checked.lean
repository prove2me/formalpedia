-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_003_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:57.080952+00:00
-- url     : https://prove2.me/theorems/906f2e63-9994-4a8e-91a1-f91f390fc6dd
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 8
-- statement:
--   For prepared pair 21, left list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 431 through 442, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_003Part08.lean, lines 10-14, SHA-256 3474230b4c5525deb5b09abf4d7522d141e9a7e9e35c78854d7ef75abd127f9a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 431) (PairLightPrepared21.leftRows.drop 431) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
