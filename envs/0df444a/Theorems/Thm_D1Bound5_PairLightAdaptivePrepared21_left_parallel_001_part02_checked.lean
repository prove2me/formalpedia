-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:45.624695+00:00
-- url     : https://prove2.me/theorems/c2c19638-a9ac-4421-a3ee-393c6efd412f
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 2
-- statement:
--   For prepared pair 21, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 106 through 117, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_001Part02.lean, lines 10-14, SHA-256 177d9a8c44d4c3a33dadde011a467fa02926cd61de77a608ad9ce887c3ee6f45. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 106) (PairLightPrepared21.leftRows.drop 106) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
