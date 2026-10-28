-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:55.118106+00:00
-- url     : https://prove2.me/theorems/fa5bec95-5b2a-4bdf-ab66-d8ea6c7232fe
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 3
-- statement:
--   For prepared pair 28, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 118 through 129, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_001Part03.lean, lines 10-14, SHA-256 ed1af8cd9175db9bfcc7e00789d01b3bc00b44956505da2a179f879560ed2bed. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 118) (PairLightPrepared28.leftRows.drop 118) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
