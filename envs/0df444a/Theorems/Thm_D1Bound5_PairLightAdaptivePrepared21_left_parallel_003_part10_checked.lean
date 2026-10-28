-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_003_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:45.351991+00:00
-- url     : https://prove2.me/theorems/7448afc5-e6e2-4b92-99a4-ffbb1654265a
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 10
-- statement:
--   For prepared pair 21, left list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 455 through 466, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_003Part10.lean, lines 10-14, SHA-256 8c63bc816be491099ad6b198c40055610419bf1c8f55922668df1488476e21d2. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 455) (PairLightPrepared21.leftRows.drop 455) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
