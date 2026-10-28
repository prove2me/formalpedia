-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:59.685523+00:00
-- url     : https://prove2.me/theorems/9eb015a6-6168-4973-a70a-7af83386062f
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 1
-- statement:
--   For prepared pair 30, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 103 through 114, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_001Part01.lean, lines 10-14, SHA-256 63b0b4c3900d1a98c203902af76972e220aba71706bc07b72f8661690f9da343. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 103) (PairLightPrepared30.leftRows.drop 103) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
